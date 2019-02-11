import os
import subprocess
import re
import argparse

def parse_args():
    parser = argparse.ArgumentParser(description='Adds loaded message to files in a directory')
    parser.add_argument('--lower', action='store_true', help='filenames to lower case letters')
    parser.add_argument('path', help='directory')
    return parser.parse_args()

def to_lowercase(fname):
    name = os.path.basename(fname)
    dir_name = os.path.dirname(fname)
    if re.match('[A-Z]', name):
        new_fname = os.path.join(dir_name, name.lower())
        subprocess.call(['git', 'mv', fname, new_fname])
        print(f'Renamed: {fname}')


def add_msg(fname, msg):
    with open(fname, 'r') as f:
        text = f.read()
        if not text.startswith('open Native'):
            return False
        if text.endswith(msg):
            return False
    with open(fname, 'a') as f:
        f.write('\n')
        f.write(msg)
    return True

def process_file(args, fname):
    if args.lower:
        to_lowercase(fname)

def main():
    args = parse_args()
    for name in os.listdir(args.path):
        fname = os.path.normpath(os.path.join(args.path, name))
        base_name, ext = os.path.splitext(name)
        if os.path.isfile(fname) and ext == '.hl':
            process_file(args, fname)
            # if add_msg(fname, f'print_endline "{fname} loaded";;'):
            #     print(f'Updated: {fname}')

if __name__ == '__main__':
    main()