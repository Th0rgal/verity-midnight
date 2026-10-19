
## Fast checks with turbo-lean (optional)

When turbo-lean is available, use it for quick checks while iterating:

```sh
turbo-lean check <File.lean> --decl <name> --project-dir .
turbo-lean check <File.lean> --project-dir .
```

lean-lsp MCP is still required for goals, diagnostics, and search. The final
judge is still `./check/check_proof.sh`.
