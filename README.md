# lemma

reference website:

https://www.lemma.cn/lean/website/index.php

the latex is printed with the aid of the following project:

https://github.com/mathjax/MathJax.git

# install
## lean
### build from binary
check https://github.com/leanprover/lean4/releases/tag/v4.18.0 to see the available installer for your system.  
for linux: (better to use VPN to download, using a browser not by wget!)
```sh
# suppose ~/gitlab is your working directory and the binary installer file is copied here.
cd ~/gitlab
# prepare zstd
# Ubuntu/Debian
sudo apt install zstd
# CentOS/RHEL
sudo yum install zstd

tar -I zstd -xf lean-4.18.0-linux.tar.zst
# tar --use-compress-program=zstd -xvf lean-4.18.0-linux.tar.zst
echo 'export PATH="$PATH:~/gitlab/lean-4.18.0-linux/bin"' >> ~/.bashrc
source ~/.bashrc

# yum install libgmp-dev
```

### build from source
install prerequisites
```sh
yum install gmp-devel 
yum install libuv libuv-devel
```

```sh
git clone https://github.com/leanprover/lean4
cd lean4
cmake --preset release
make -C build/release -j$(nproc || sysctl -n hw.logicalcpu)
```

## elan
check https://github.com/leanprover/elan/releases/tag/v4.0.0 to see available installer for your system.  
for linux:  
```sh
# suppose ~/gitlab is your working directory
cd ~/gitlab
wget https://github.com/leanprover/elan/releases/download/v4.0.0/elan-x86_64-unknown-linux-gnu.tar.gz
tar -xzf elan-x86_64-unknown-linux-gnu.tar.gz
# ./elan-init -y --default-toolchain stable
# skipping the stable default-toolchain installation
./elan-init -y
# check environment settings, or restart your terminal
cat ~/.bashrc
cat ~/.bash_profile
cat ~/.profile
elan toolchain link v4.18.0 ~/gitlab/lean-4.18.0-linux
elan default v4.18.0
elan show

lake --version
lean --version
elan --version
# update elan using command
elan self update
```

### install lean using elan
this is not suggested due to slow network.
```sh
elan toolchain install stable
elan default stable
```

## Update mathlib4 using commit-id
copy the content of https://github.com/leanprover-community/mathlib4/blob/aa936c36e8484abd300577139faf8e945850831a/lake-manifest.json and replace your own version with it. Then use the following script to automatically and incrementally update the dependency git projects required by mathlib4
```sh
bash sh/update.sh
```

# trouble-shooting for VSCode

## Error loading webview

Error: Could not register service worker: InvalidStateError: Failed to register a ServiceWorker: The document is in an invalid state..

### solution
Clear VSCode's Cache: If some cached data is causing the error, clearing the cache might help.

Remove cache directories:
- [ ] On Windows: C:\Users\<YourUsername>\AppData\Roaming\Code
- [ ] On Mac: ~/Library/Application Support/Code
- [ ] On Linux: ~/.config/Code

Be cautious with this step as it will reset some settings and extensions might need re-installation.

## Network Issue when installing from github
solutions:
- [ ] install Lean4 extension in VSCode
- [ ] find a linux machine that can use lean4 with no problem, and then scp -r ~/.elan yourName@TargetIPAddress:
- [ ] echo 'export PATH="$HOME/.elan/bin:$PATH"' >> ~/.profile on the Target machine
- [ ] scp -r yourLeanProject yourName@TargetIPAddress:targetFolder/
Now you can work on yourLeanProject on your Target machine with no trouble.

# related projects
https://github.com/ImperialCollegeLondon/FLT

# paper to read
```
https://zhuanlan.zhihu.com/p/695704489
https://github.com/Goedel-LM/Goedel-Prover
https://github.com/deepseek-ai/DeepSeek-Prover-V1.5
https://arxiv.org/abs/2408.08152v1
https://arxiv.org/abs/2502.03438
https://aclanthology.org/2024.emnlp-main.667
https://github.com/leanprover-community/repl
https://leanprover-community.github.io/mathlib4_docs/index.html
https://arxiv.org/abs/2504.06122
https://mml-book.github.io/book/mml-book.pdf
https://mml-book.github.io/
https://help.aliyun.com/zh/model-studio/what-is-model-studio
https://arxiv.org/abs/2504.11354
```
cd repl
lake update -R && lake build
lake exe repl

# lean-web
https://live.lean-lang.org/
https://github.com/leanprover-community/lean4web/blob/main/doc/Usage.md
https://www.leanprover.cn/projects/lean4web/
https://github.com/hhu-adam/lean4web-tools
https://github.com/leanprover-community/lean4web


# incremental parsing
To render code blocks dynamically in Vue 3 as content streams character-by-character from an LLM, follow these steps:

### 1. Set Up Reactive State and Parsing Logic

```vue
<script setup lang="ts">
import { ref, reactive, watch, onMounted } from 'vue';
import Prism from 'prismjs';
import 'prismjs/themes/prism.css';
// Import required languages (e.g., javascript, python)
import 'prismjs/components/prism-javascript';
import 'prismjs/components/prism-python';

// Define segment types
type TextSegment = { type: 'text'; content: string };
type CodeSegment = { type: 'code'; content: string; language?: string };
type Segment = TextSegment | CodeSegment;

const closedSegments = ref<Segment[]>([]);
const pendingSegment = ref<CodeSegment | null>(null);

const processingState = reactive({
  mode: 'text' as 'text' | 'language' | 'code',
  textBuffer: '',
  languageBuffer: '',
  currentLanguage: '',
});

// Process incoming streamed text
function processStreamedContent(newContent: string) {
  for (const char of newContent) {
    if (processingState.mode === 'text') {
      processingState.textBuffer += char;
      if (processingState.textBuffer.endsWith('```')) {
        // Add text before ```
        const textContent = processingState.textBuffer.slice(0, -3);
        if (textContent) {
          closedSegments.value.push({ type: 'text', content: textContent });
        }
        // Switch to language mode
        processingState.mode = 'language';
        processingState.textBuffer = '';
      }
    } else if (processingState.mode === 'language') {
      if (char === '\n') {
        processingState.currentLanguage = processingState.languageBuffer.trim();
        processingState.mode = 'code';
        pendingSegment.value = {
          type: 'code',
          content: '',
          language: processingState.currentLanguage,
        };
        processingState.languageBuffer = '';
      } else {
        processingState.languageBuffer += char;
      }
    } else if (processingState.mode === 'code') {
      if (pendingSegment.value) {
        pendingSegment.value.content += char;
        // Check for closing ```
        if (pendingSegment.value.content.endsWith('```')) {
          // Add to closed segments without ```
          closedSegments.value.push({
            type: 'code',
            content: pendingSegment.value.content.slice(0, -3),
            language: pendingSegment.value.language,
          });
          pendingSegment.value = null;
          processingState.mode = 'text';
          processingState.currentLanguage = '';
        }
      }
    }
  }

  // Handle remaining text after processing
  if (processingState.mode === 'text' && processingState.textBuffer) {
    closedSegments.value.push({
      type: 'text',
      content: processingState.textBuffer,
    });
    processingState.textBuffer = '';
  }
}
</script>
```

### 2. Create a Code Highlight Component

```vue
<!-- CodeBlock.vue -->
<script setup lang="ts">
import { ref, watch, onMounted } from 'vue';
import Prism from 'prismjs';

const props = defineProps<{
  content: string;
  language?: string;
}>();

const codeEl = ref<HTMLElement>();

function highlight() {
  if (codeEl.value) {
    codeEl.value.textContent = props.content; // Update content
    Prism.highlightElement(codeEl.value);
  }
}

onMounted(highlight);
watch(() => props.content, highlight, { flush: 'post' });
</script>

<template>
  <pre><code :class="`language-${language}`" ref="codeEl"></code></pre>
</template>
```

### 3. Implement the Main Component Template

```vue
<template>
  <div class="stream-output">
    <div v-for="(segment, index) in closedSegments" :key="index">
      <template v-if="segment.type === 'text'">
        {{ segment.content }}
      </template>
      <CodeBlock
        v-else
        :content="segment.content"
        :language="segment.language"
      />
    </div>
    <CodeBlock
      v-if="pendingSegment"
      :content="pendingSegment.content"
      :language="pendingSegment.language"
    />
  </div>
</template>
```

### 4. Usage Example with Streamed Data

```vue
<script setup lang="ts">
// Simulate streamed content (replace with actual SSE/WebSocket logic)
const responseText = ref('');
let simulatedResponse = `
Here's an example:
\`\`\`python
def greet():
    print("Hello")

greet()
\`\`\`
And another:
\`\`\`javascript
function hello() {
  console.log('World');
}
\`\`\`
`;

// Simulate character-by-character streaming
let i = 0;
const interval = setInterval(() => {
  if (i < simulatedResponse.length) {
    responseText.value += simulatedResponse[i];
    processStreamedContent(simulatedResponse[i]);
    i++;
  } else {
    clearInterval(interval);
  }
}, 50);
</script>
```

### Key Features:
- **Incremental Parsing**: Detects code blocks in real-time as text streams in.
- **State Management**: Tracks parsing state (text/code mode) across character chunks.
- **Dynamic Highlighting**: Applies syntax highlighting using Prism.js as content updates.
- **Pending Code Blocks**: Shows incomplete code blocks while they're being received.

### Notes:
- Ensure you import all required Prism.js language components.
- Adjust the streaming simulation interval (50ms) to match your actual data source.
- Handle edge cases like unterminated code blocks by displaying raw content if streaming stops.

To render streaming Markdown content dynamically in Vue 3 as it arrives character-by-character, follow this optimized implementation:

```vue
<template>
  <div class="markdown-output" ref="markdownContainer"></div>
</template>

<script setup>
import { ref, onMounted, watchEffect } from 'vue'
import MarkdownIt from 'markdown-it'
import hljs from 'highlight.js'

// Reactive state
const markdownText = ref('')
const markdownContainer = ref(null)

// Markdown parser with syntax highlighting
const md = new MarkdownIt({
  html: true,
  highlight: (str, lang) => {
    if (lang && hljs.getLanguage(lang)) {
      try {
        return `<pre class="hljs"><code>${
          hljs.highlight(str, { language: lang, ignoreIllegals: true }).value
        }</code></pre>`
      } catch (__) {}
    }
    return `<pre class="hljs"><code>${md.utils.escapeHtml(str)}</code></pre>`
  }
})

// Progressive rendering setup
let buffer = []
let renderQueue = Promise.resolve()

const appendContent = (chunk) => {
  buffer.push(chunk)
  
  // Schedule rendering in microtask queue
  renderQueue = renderQueue.then(() => {
    if (buffer.length > 0) {
      markdownText.value += buffer.join('')
      buffer = []
      updateDisplay()
    }
  })
}

const updateDisplay = () => {
  if (!markdownContainer.value) return
  
  // Get current scroll state
  const container = markdownContainer.value
  const shouldScroll = container.scrollTop + container.clientHeight >= container.scrollHeight - 50

  // Render markdown
  const html = md.render(markdownText.value)
  container.innerHTML = html

  // Apply syntax highlighting
  container.querySelectorAll('pre code').forEach(block => {
    if (!block.classList.contains('hljs')) {
      hljs.highlightElement(block)
    }
  })

  // Maintain scroll position
  if (shouldScroll) {
    container.scrollTop = container.scrollHeight
  }
}

// Handle stream updates
watchEffect(updateDisplay)

// Simulate stream (replace with actual SSE/WebSocket connection)
onMounted(() => {
  const simulateStream = async () => {
    const sampleText = "## Streaming Markdown\n\n```javascript\nconsole.log('Hello')\n```\n\n**Bold text**...\n"
    for (const char of sampleText) {
      appendContent(char)
      await new Promise(resolve => setTimeout(resolve, 20))
    }
  }
  
  simulateStream()
})
</script>

<style>
.markdown-output {
  max-height: 500px;
  overflow-y: auto;
  padding: 1rem;
  border: 1px solid #ccc;
}

.hljs {
  padding: 1rem;
  border-radius: 4px;
  background: #f8f8f8;
}

.markdown-output h1, .markdown-output h2 {
  border-bottom: 1px solid #eee;
  padding-bottom: 0.3em;
}
</style>
```

Key features of this implementation:

1. **Chunk Buffering**: Aggregates incoming characters into batches for more efficient rendering
2. **Asynchronous Rendering**: Uses a promise chain to handle rendering in the microtask queue
3. **Syntax Highlighting**: Integrates Highlight.js for code blocks with caching to avoid redundant processing
4. **Scroll Management**: Maintains scroll position automatically as new content arrives
5. **Performance Optimizations**:
   - Batch processing of incoming characters
   - DOM updates only when needed
   - Cached highlighting of already processed code blocks
   - Efficient Markdown parsing with markdown-it

To integrate with an actual LLM stream:

1. Replace the `simulateStream` function with real streaming code:
```javascript
const setupRealStream = () => {
  const eventSource = new EventSource('/api/stream')
  
  eventSource.onmessage = (event) => {
    appendContent(event.data)
  }

  eventSource.onerror = (error) => {
    console.error('Stream error:', error)
    eventSource.close()
  }
}
```

2. For WebSocket implementations:
```javascript
const setupWebSocket = () => {
  const ws = new WebSocket('wss://your-endpoint')
  
  ws.onmessage = (event) => {
    appendContent(event.data)
  }
}
```

This solution provides:
- Progressive rendering of Markdown elements
- Efficient handling of frequent updates
- Proper code block formatting and highlighting
- Smooth scrolling behavior
- Clean separation of parsing and rendering concerns

The implementation balances responsiveness with performance by using batched updates and efficient DOM manipulation techniques.