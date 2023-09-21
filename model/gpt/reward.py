from std.http import json_post

import Levenshtein
def similarity(lhs, rhs):
    return 1 - Levenshtein.distance(lhs, rhs) / max(len(lhs), len(rhs))

class RewardModel:

    def __init__(self):
        ...
        
    def create_model(self):
        ...

    def __call__(self, latex, python):
        result = json_post('http://192.168.18.132:5000/eval', dict(python=python))
        
        if isinstance(result, str):
            print(result)
            print(python)
            return 0
        
        if 'latex' in result:
            return similarity(latex, result['latex'])
        elif 'error' in result:
            print(result['error'])
            print(python)
            return 0

            
instance = RewardModel()

def test_reward():
    from std import MySQL
    # from model.gpt.sft import instance
    for id, latex, python, training in MySQL.instance.select('latex', fetch_size=10, limit=100000):
        text = latex + '\nPython codes yielding the latex above:\n'
        # result = dict(text=instance('facebook/opt-350m/latex', text))
        result = json_post('http://192.168.18.100:5002/generate/facebook/opt-350m/latex', dict(text=text))
        if isinstance(result, str):
            print(result)
        else:
            python = result['text']
            score = instance(latex, python)
            print('score =', score)
            
if __name__ == '__main__':
    test_reward()