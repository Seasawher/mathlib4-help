Get-ChildItem -Path src -Exclude SUMMARY.md | Remove-Item -Force -Recurse

lake env lean --run Lean/Tactic.lean > src/tactics.md
lake env lean --run Lean/Option.lean > src/options.md
lake env lean --run Lean/Command.lean > src/commands.md
lake env lean --run Lean/Attribute.lean > src/attributes.md
