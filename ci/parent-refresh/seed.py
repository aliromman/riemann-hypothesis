"""Retry a transient curl failure with the already verified archives on this runner."""
import argparse
from pathlib import Path
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / 'current-recheck'))
from parent import Authority, seed

TRANSIENT_CURL = {5, 6, 7, 18, 28, 35, 52, 55, 56, 92}


def retry_seed(parent, cache, authority, *, prepare=seed, wait=time.sleep):
    for attempt in range(4):
        try:
            return prepare(parent, cache, authority)
        except subprocess.CalledProcessError as error:
            if (attempt == 3 or not isinstance(error.cmd, (list, tuple))
                    or Path(error.cmd[0]).name != 'curl' or error.returncode not in TRANSIENT_CURL):
                raise
            print(f'Transient curl exit {error.returncode}. Retry with verified archives on disk.', flush=True)
            wait(4 * 2**attempt)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    for arg in ('parent', 'cache', 'authority'):
        parser.add_argument('--' + arg, type=Path, required=True)
    args = parser.parse_args()
    retry_seed(args.parent, args.cache, Authority.read(args.authority))
