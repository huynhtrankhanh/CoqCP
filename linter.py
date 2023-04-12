import argparse
import os
from pathlib import Path
import re
import sys

def lint_coq_file(filename, spaces, max_line_length):
    print(f"Linting {filename}...")
    with open(filename, 'r') as file:
        lines = file.readlines()

    issues = []

    line_number = 1
    last_line_blank = False
    prev_indentation = 0

    operators = [r'\b->\b', r'\b<->\b', r'\b/\\\b', r'\b\\/\b', r'\b=\b', r'\b<\b', r'\b>\b', r'\b<=\b', r'\b>=\b', r'\b<>\b',
             r'\b&&\b', r'\b\|\|\b', r'\b<=\?\b', r'\b>=\?\b', r'\b<\?\b', r'\b>\?\b']

    operators_without_boundaries = ['->', '<->', '/\\', '\\/', '=', '<', '>', '<=', '>=', '<>',
                                '&&', '||', '<=?', '>=?', '<?', '>?']

    for line in lines:
        stripped_line = line.rstrip()
        indentation = len(line) - len(line.lstrip())

        if stripped_line:  # Add this condition to check if the line is not empty
            if indentation % spaces != 0:
                issues.append(f"Line {line_number}: Incorrect indentation (found {indentation} spaces, should be a multiple of {spaces})")
            elif indentation > prev_indentation + spaces and prev_indentation != 0:
                issues.append(f"Line {line_number}: Invalid indentation jump (found {indentation} spaces, can only increase by {spaces} spaces at a time)")

        if re.search(r'[ \t]+$', line):
            issues.append(f"Line {line_number}: Trailing spaces or tabs found")

        if not stripped_line and last_line_blank:
            issues.append(f"Line {line_number}: Consecutive blank lines found")
            issues_found += 1

        if len(line) > max_line_length:
            issues.append(f"Line {line_number}: Line exceeds maximum length of {max_line_length} characters")

        if "Admitted." in stripped_line:
            issues.append(f"Line {line_number}: 'Admitted' found, incomplete proofs are not allowed")

        for index, op in enumerate(operators):
            if re.search(fr'{op}', stripped_line):
                issues.append(f"Line {line_number}: Missing spaces around operator '{operators_without_boundaries[index]}'")

        last_line_blank = not stripped_line
        prev_indentation = indentation if stripped_line else prev_indentation  # Only update prev_indentation for non-empty lines
        line_number += 1
    return issues


def lint_all_coq_files(root_dir, spaces, max_line_length):
    all_issues = {}
    for dirpath, dirnames, filenames in os.walk(root_dir):
        for filename in filenames:
            if filename.endswith('.v'):
                issues_found = lint_coq_file(os.path.join(dirpath, filename), spaces, max_line_length)
                if issues_found:
                    all_issues[os.path.join(dirpath, filename)] = issues_found

    return all_issues

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="A simple linter for Coq files.")
    parser.add_argument('-d', '--directory', type=str, default=str(Path(__file__).resolve().parent), help="The root directory to start scanning for Coq files (default: current directory).")
    parser.add_argument('-s', '--spaces', type=int, default=2, help="The number of spaces for each indentation level (default: 2).")
    parser.add_argument('-m', '--max-line-length', type=int, default=1800, help="The maximum line length (default: 1800 characters).")
    args = parser.parse_args()
    issues = lint_all_coq_files(args.directory, args.spaces, args.max_line_length)
    print()

    for k, v in issues.items():
        print(f'File {k}:')
        for issue in v:
            print(issue)
        print()

    if not issues:
        print("No issues found!")
        sys.exit(0)
    else:
        print(f"Total issues found: {sum(len(v) for v in issues.values())}")
        sys.exit(1)
