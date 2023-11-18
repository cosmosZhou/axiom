from transformers import AutoTokenizer, AutoModelForCausalLM
from std import computed
import os, json, std
import torch.nn.functional as F
import torch

class GPTInstance:
    '''
    ('input_ids', 'attention_mask'), 'labels'
    '''

    def __init__(self, input_ids, labels, attention_mask):
        self.input_ids = input_ids
        self.labels = labels
        self.attention_mask = attention_mask

class Instance:
    
    max_seq_len = 2048
    def __init__(self, id, input, target, training, **kwargs):
        self.id = id
        self.input = input
        self.target = target
        self.training = training

    def convert_example(self, tokenizer):
        assert self.target
        prompt = '\nPython codes yielding the latex above:\n'
        inp = tokenizer(f"{self.input}{prompt}")['input_ids']
        oup = tokenizer(f"{self.target}</s>")['input_ids'][1:]

        input_ids = inp + oup
        labels = [-100] * len(inp) + oup
        
        if len(input_ids) > self.max_seq_len:
            input_ids = input_ids[:self.max_seq_len]
            labels = labels[:self.max_seq_len]
        
        return GPTInstance(input_ids, labels, [1] * len(input_ids))


from std.keras import KerasModel
from util import utility

class SFTModel(KerasModel):

    learning_rate = 1e-5
    epochs = 10
    batch_size = 8
    weight_decay = 0.0
    class_weight = None
    label_smoothing = 0.0
    # training = False, for prediction purposes;
    # training = True,  for training from scratch, this will delete the previously trained model;
    # training = None,  for continue training;
    def __init__(self, modelPretrained, table, training=None):
        self.table = table
        if not modelPretrained.endswith('/'):
            modelPretrained += '/'

        self.modelPretrained = modelPretrained
        self.modelPath = self.modelPretrained + table + '/'
        self.modelFile = self.modelPath + 'pytorch_model.bin'

        if training and os.path.exists(self.modelFile):
            try:
                os.remove(self.modelFile)
            except FileNotFoundError:
                ...

        if not os.path.exists(self.modelFile):
            import shutil
            from std.file import createNewPath
            createNewPath(self.modelPath)
            for file in std.listdir(self.modelPretrained, None):
                if os.path.isfile(file) and not file.startswith('pytorch_model'):
                    shutil.copy(file, self.modelPath + os.path.basename(file))

        extra_kwargs = {}
        if torch_dtype := json.load(open(self.modelPath + 'config.json')).get('torch_dtype'):
            if torch.cuda.is_available():
                extra_kwargs['torch_dtype'] = getattr(torch, torch_dtype)

        self.model = AutoModelForCausalLM.from_pretrained(
            self.modelPretrained if training else self.modelPath, 
            **extra_kwargs)

        tokenizer_config = self.modelPath + 'tokenizer_config.json'
        if os.path.exists(tokenizer_config) and (tokenizer_class := json.load(open(tokenizer_config)).get('tokenizer_class')):
            import transformers
            tokenizer_class = getattr(transformers, tokenizer_class)
        else:
            tokenizer_class = AutoTokenizer
        self.vocab = tokenizer_class.from_pretrained(modelPretrained)
        self.vocab.pad_token_id = 0
        # assert not self.model.config.pad_token_id
        args, kwargs = std.argparse()
        if kwargs['zero_stage'] == 3:
            self.args = (modelPretrained, table)
        elif not kwargs['deepspeed']:
            super().__init__()
            self.args = kwargs

    @property
    def lang(self):
        for token in self.modelPath.split('/'):
            if token in ('en', 'cn', 'jp', 'kr', 'fr', 'de'):
                return token

    def __call__(self, text):
        device = 'cuda:0' if torch.cuda.is_available() else 'cpu'
        # text += '[AI]'
        prefix_length = len(text)
        vocab = self.vocab
        input_ids = vocab(text, return_tensors="pt")["input_ids"]
        if input_ids.shape[1] > 1024:
            print(f'warning! The text given too long, shrunk to 1024 tokens:\n{text}')
            input_ids = input_ids[:, -1024:]
            text = vocab.decode(input_ids[0])
            prefix_length = len(text)

        model = self.model
        generation_config = dict(
            temperature=0.7,
            top_k=40,
            top_p=0.9,
            do_sample=True,
            repetition_penalty=1.13,
            max_new_tokens=1024)
        
        generation_output = model.generate(
            input_ids=input_ids.to(device),
            eos_token_id=vocab.eos_token_id,
            **generation_config) 
        generation_output = [vocab.decode(x, skip_special_tokens=True)[prefix_length:].lstrip() for x in generation_output]
        if len(generation_output) == 1:
            generation_output, = generation_output
        return generation_output

    def forward(self, *args):
        return self.model.forward(*args).logits

    @computed
    def table_info(self):
        from std import MySQL
        textField = []
        with MySQL.instance as instance:
            for Field, Type, Collation, Null, Key, Default, Extra, Privileges, Comment in instance.query(f"show full columns from {self.table}"):
                if isinstance(Type, bytes):
                    Type = Type.decode()
    
                if Type == 'text':
                    textField.append(Field)

        return textField
    
    @computed
    def inputField(self):
        return self.table_info[0]

    @computed
    def targetField(self):
        return self.table_info[1]
    
    def load_data(self, training=1, **kwargs):
        from std import MySQL
        inputField = self.inputField
        targetField = self.targetField
        from tqdm import tqdm
        with MySQL.instance as instance:
            if lang := self.lang:
                kwargs['lang'] = lang
            data = instance.select(self.table, training=training, dictionary=True, **kwargs)
            for kwargs in tqdm(data):
                kwargs['input'], kwargs['target'] = kwargs[inputField], kwargs[targetField]
                yield Instance(**kwargs).convert_example(self.vocab)

    def loss(self, y_true, y_pred):
        # import pydevd; pydevd.settrace('172.16.11.42')
        return F.cross_entropy(
            y_pred[..., :-1, :].reshape(-1, y_pred.shape[-1]), 
            y_true[..., 1:].reshape(-1),
            reduction='none')

    def accuracy(self, y_true, y_pred):
        # import pydevd; pydevd.settrace('172.16.11.42')
        y_pred = y_pred[..., :-1, :]
        y_true = y_true[..., 1:]
        
        y_pred = y_pred.argmax(dim=-1)
        judge = y_pred == y_true
        judge |= y_true <= 0
        return judge.all(1) # determine the sentence level accuracy


class ModelInstance:
    def __init__(self, path=utility.assetsDirectory()):
        self.path = path

    def __getitem__(self, attr, training=None):
        model = self.__dict__.get(attr, None)
        if model is None:
            if os.path.isdir(self.path + attr):
                if os.path.exists(self.path + 'pytorch_model.bin') or os.path.exists(self.path + 'pytorch_model.bin.index.json'):
                    model = SFTModel(self.path, attr, training=training)
                else:
                    model = ModelInstance(self.path + attr + '/')
            else:
                model = SFTModel(self.path, attr)
            self.__dict__[attr] = model

        return model
    
    def training(self, path, *args, **kwargs):
        if kwargs.get('continue', True):
            training = None
        else:
            training = True
        for path in path.split('/'):
            self = self.__getitem__(path, training=training)
        self.training(*args, **kwargs)

    def evaluate(self, path, *args, **kwargs):
        for path in path.split('/'):
            self = self.__getitem__(path, training=False)

        self.evaluate(*args, **kwargs)

    def __call__(self, path, *args, **kwargs):
        for path in path.split('/'):
            self = self.__getitem__(path, training=False)

        return self(*args, **kwargs)
        

instance = ModelInstance()