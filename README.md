# Mathlib4 Help

This is a list of the output of `#help` command of mathlib4. see [GitHub Page](https://seasawher.github.io/mathlib4-help/)!

This is heavily inspired by [haruhisa-enomoto/mathlib4-all-tactics](https://github.com/haruhisa-enomoto/mathlib4-all-tactics).

This web page is automatically updated by GitHub Action.

## How to install dependencies

```pwsh
# activate virtual environment
py -m venv .venv
.venv\Scripts\activate

# install dependencies
pip install -r requirements.txt
```

## How to generate markdown file

First, install Lean and Python 3.10, and then run the following commands:

```pwsh
./scripts/build.ps1
python3 script.py
```

## How to serve website

```pwsh
python -m mkdocs serve
```
