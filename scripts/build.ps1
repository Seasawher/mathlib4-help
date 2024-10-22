Get-ChildItem -Path docs -Exclude SUMMARY.md | Remove-Item -Force -Recurse

lake env lean --run Lean/Tactic.lean > docs/tactics.md
lake env lean --run Lean/Option.lean > docs/options.md
lake env lean --run Lean/Command.lean > docs/commands.md
lake env lean --run Lean/Attribute.lean > docs/attributes.md
