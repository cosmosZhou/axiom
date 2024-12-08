# axiom

reference website:

https://www.axiom.top/axiom/website/index.php

the latex is printed with the aid of the following project:

https://github.com/mathjax/MathJax.git


# Update mathlib4 commit-id

## Check Commit ID
get the commit rev from lake-manifest.json for mathlib4
say: 87ee1f25bf4ee48b5290edf466511e6e76d7286a

## Fetch the Latest Changes
Ensure your local repository is up-to-date with the remote repository. You can do this by running:
```bash
# If the repository is very large, increasing Git's buffer size might help. You can do this by setting the http.postBuffer option:
# git config --global http.postBuffer 524288000
# git fetch origin
git fetch --depth 1 origin 87ee1f25bf4ee48b5290edf466511e6e76d7286a
```
This command fetches only a limited number of commits from the history, which can significantly reduce the amount of data transferred.

## Checkout the Commit
Now, you can check out the specific commit specified by lake-manifest.json:
```bash
git checkout 87ee1f25bf4ee48b5290edf466511e6e76d7286a
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
