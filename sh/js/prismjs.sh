# List all files to download
urls=(
  "unpkg.com/prismjs@1.30.0/prism.js"
  "unpkg.com/prismjs@1.30.0/components/prism-python.min.js"
  "unpkg.com/prismjs@1.30.0/components/prism-javascript.min.js"
  "unpkg.com/prismjs@1.30.0/components/prism-typescript.min.js"
  "unpkg.com/prismjs@1.30.0/components/prism-php.min.js"
  "unpkg.com/prismjs@1.30.0/components/prism-c.min.js"
  "unpkg.com/prismjs@1.30.0/components/prism-cpp.min.js"
  "unpkg.com/prismjs@1.30.0/components/prism-java.min.js"
  "unpkg.com/prismjs@1.30.0/components/prism-css.min.js"
  "unpkg.com/prismjs@1.30.0/components/prism-bash.min.js"
  "unpkg.com/prismjs@1.30.0/components/prism-json.min.js"
  "unpkg.com/prismjs@1.30.0/themes/prism.min.css"
)

# Process each URL
for url in "${urls[@]}"; do
  # Remove filename from path
  dir="static/${url%/*}"
  # Create directory 
  mkdir -p "$dir"
  (cd "$dir" && wget -nc "https://$url")  # Download file
done