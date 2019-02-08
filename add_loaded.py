import os
import argparse

def parse_args():
    parser = argparse.ArgumentParser(description='Adds loaded message to files in a directory')
    parser.add_argument('path', help='directory')
    return parser.parse_args()

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

def main():
    args = parse_args()
    for name in os.listdir(args.path):
        fname = os.path.normpath(os.path.join(args.path, name))
        base_name, ext = os.path.splitext(name)
        if os.path.isfile(fname) and ext == '.hl':
            if add_msg(fname, f'print_endline "{fname} loaded";;'):
                print(f'Updated: {fname}')

if __name__ == '__main__':
    main()