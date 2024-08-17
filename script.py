import re

targets = ["tactic", "option"]

file_path_dict = {
  "tactic": "src/tactics.md",
  "option": "src/options.md"
}

pattern_dict = {
  "tactic": r'syntax "(.*?)".*?\[(.*)\]',
  "option": r"option (.*) : (.*) := (.*)"
}

replacement_dict = {
  "tactic": r"# \1\nDefined in: `\2`\n",
  "option": r"## \1\ntype: `\2`\ndefault: `\3`"
}

def format(target : str):
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

  # replace mere code blocks with lean code blocks
  new_content = re.sub(r'(^|.*:|[a-zA-Z]+\.)\n```\n', r'\1\n```lean\n', new_content)

  content_with_version = 'Lean version: `{{#include ../lean-toolchain}}`\n\n' + new_content

  with open(file_path, 'w', encoding='utf-8') as file:
    file.write(content_with_version)

if __name__ == '__main__':
  for target in targets:
    format(target)
