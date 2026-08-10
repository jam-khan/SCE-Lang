# SCE-Lang for VS Code

Syntax highlighting for `.sce` and `.scei` files: nested `(* *)` comments,
strings, the keyword set from `lib/source/lexer.mll`, builtin types, the merge
operators `,,` / `,,,`, arrows, and `;;` top-level markers.

## Install (local)

Symlink the extension into your extensions directory and reload VS Code:

```console
$ ln -s "$(pwd)/editors/vscode/sce" ~/.vscode/extensions/sce-lang.sce-lang-0.1.0
```

Then run **Developer: Reload Window**. To package a `.vsix` instead:

```console
$ npx @vscode/vsce package
$ code --install-extension sce-lang-0.1.0.vsix
```
