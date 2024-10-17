import re
from json import load

targets = ["tactic", "option", "command", "attribute"]

file_path_dict = {
  "tactic": "src/tactics.md",
  "option": "src/options.md",
  "command": "src/commands.md",
  "attribute": "src/attributes.md"
}

pattern_dict = {
  "tactic": r'syntax "(.*?)".*?\[(.*)\]',
  "option": r"option (.*) : (.*) := (.*)",
  "command": r'syntax "(.*?)".*?\[(.*)\]',
  "attribute": r"\[(.*)\]:"
}

replacement_dict = {
  "tactic": r"## \1\nDefined in: `\2`\n",
  "option": r"## \1\ntype: `\2`\n\ndefault: `\3`\n",
  "command": r"## \1\nDefined in: `\2`\n",
  "attribute": r"## \1\n"
}

def format(target : str):
  """
  Format the content of the file
  """
  if target not in targets:
    raise ValueError(f"target must be one of {targets}")

  file_path = file_path_dict[target]

  pattern = pattern_dict[target]

  replacement = replacement_dict[target]

  with open(file_path, 'r', encoding='utf-8') as file:
    # delete leading spaces
    content = "".join([re.sub(r'^\s\s', '', line) for line in file])

  # create markdown-style headers
  new_content = re.sub(pattern, replacement, content)

  # escape `#` in headers
  new_content = re.sub(r"(#+) #", r"\1 \#", new_content)

  # replace mere code blocks with lean code blocks
  new_content = re.sub(r'(^|.*:|[a-zA-Z]+\.)\n```\n', r'\1\n```lean\n', new_content)

  with open(file_path, 'w', encoding='utf-8') as file:
    file.write(new_content)

def mathlib_version() -> str:
  """
  Read `lake-manifest.json` and return the hash of the mathlib
  """
  with open('lake-manifest.json', 'r', encoding='utf-8') as file:
    data = load(file)

  packages : list[str] = data["packages"]
  version = ""
  for package in packages:
    if "mathlib" == package["name"]:
      version = package["rev"]
      break
  return version

def add_header(target : str) -> None:
  """
  Add header to the beginning of the file
  """
  file_path = file_path_dict[target]

  with open(file_path, 'r', encoding='utf-8') as file:
    content = file.read()

  header = f"# {target.capitalize()}s\n\n"
  version_info = f"Mathlib version: `{mathlib_version()}`\n\n"
  new_content = header + version_info + content

  with open(file_path, 'w', encoding='utf-8') as file:
    file.write(new_content)

if __name__ == '__main__':
  for target in targets:
    format(target)
    add_header(target)
