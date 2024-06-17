# Mathlib4 Tactics

This is a list of all mathlib4 tactics. see [GitHub Page](https://seasawher.github.io/mathlib4-tactics/)!

This is heavily inspired by [haruhisa-enomoto/mathlib4-all-tactics](https://github.com/haruhisa-enomoto/mathlib4-all-tactics).

This web page is automatically updated by GitHub Action.

## How to generate markdown file

First, install Lean and Python 3.10, and then run the following commands:

```bash
rm .\src\tactics.md
lake env lean --run Main.lean > src/tactics.md
python3 script.py
```
