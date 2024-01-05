import os
import subprocess
import sys
from typing import NoReturn, Self


def main():
    config = Config.parse_arg(sys.argv)
    tester = Tester(config)
    tester.test_all()


class Config:
    def __init__(self, *, test_directory: str, options: list[str]):
        self.test_directory = test_directory
        self.options = options

    @classmethod
    def parse_arg(cls, args: list[str]) -> Self:
        if len(args) == 1 or any(
            option in args for option in ("-h", "--help", "-help")
        ):
            help()

        directory = args[1]
        if not os.path.isdir(directory):
            error(f'The directory "{directory}" does not exist.')

        return cls(test_directory=directory, options=args[2:])


class Tester:
    def __init__(self, config: Config):
        self.files = list_files(config.test_directory)
        self.options = config.options
        self.build()

    def build(self):
        command = ["dune", "build", "test.exe"]
        res = subprocess.run(command)
        if res.returncode:
            exit(1)

    def test_all(self):
        for file in self.files:
            self.test(file)

    def test(self, file: str):
        command = [
            "_build/default/test.exe",
            "-intrinsics",
            "stdlib/lin.intr",
            *self.options,
            file,
        ]
        res = subprocess.run(command, capture_output=True, text=True)
        output = res.stdout.strip() + res.stderr.strip()
        print(output + ":", file)


def help() -> NoReturn:
    print("python test.py <directory> [options]")
    print("directory: the directory including *.imp")
    print("options: options of test.sh. See `$ ./test.sh --help`")
    exit(0)


def list_files(path: str) -> list[str]:
    res: list[str] = []
    for root, _, files in os.walk(path):
        for file in files:
            file_path = os.path.join(root, file)
            if file_path.endswith(".imp"):
                res.append(file_path)
    return res


def error(message) -> NoReturn:
    print(message)
    exit(1)


if __name__ == "__main__":
    main()
