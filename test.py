import std
from os.path import dirname
for file in std.listdir(dirname(__file__), sufix='.py', recursive=True):
    print(file)
    std.eol_convert(file)