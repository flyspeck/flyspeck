import os
import subprocess
import re
import argparse

def parse_args():
    parser = argparse.ArgumentParser(description='Adds loaded message to files in a directory')
    parser.add_argument('--lower', action='store_true', help='filenames to lowercase letters')
    parser.add_argument('--add', action='store_true', help='add headers and footers')
    parser.add_argument('path', help='directory')
    return parser.parse_args()

def to_lowercase(fname):
    name = os.path.basename(fname)
    dir_name = os.path.dirname(fname)
    if re.match('[A-Z]', name):
        new_fname = os.path.join(dir_name, name.lower())
        subprocess.call(['git', 'mv', fname, new_fname])
        print(f'Renamed: {fname}')

DEF_OPEN = [
    'Card',
    'Iter',
    'Products',
    'Permutations',
    'Misc',
    'Vectors',
    'Determinants',
    'Metric',
    'Topology',
    'Convex',
    'Polytope',
    'Integration',
    'Measure',
    'Complexes',
    'Transcendentals',
    'Realanalysis',
    'Geom',
    'Cross',
    'Flyspeck'
]

def add_header_footer(fname):
    with open(fname, 'r') as f:
        text = f.read()
        if text.startswith('open Native'):
            return
    open_text = '\n'.join(f'open {name};;' for name in DEF_OPEN)
    with open(fname, 'w') as f:
        f.write('open Native_strictbuild;;\nload_begin();;\n\n')
        f.write(open_text + '\n\n')
        f.write(text)
        f.write('\n\nload_end __FILE__;;')
    print(f'Updated: {fname}')

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
    if args.add:
        add_header_footer(fname)

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