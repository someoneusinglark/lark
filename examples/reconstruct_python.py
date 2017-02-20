from .python_parser import python_parser2, python_parser3

from lark import Lark
from lark.reconstruct import Reconstructor
from lark.lexer import Token

def test():

    test_code = '''
print("Hello World!")
'''

    tree = python_parser3.parse(test_code)

    next(tree.find_data('string')).children[0] = Token('STRING', '"New text"')

    new_code = Reconstructor(python_parser3).reconstruct(tree)
    print new_code

    print(python_parser3.parse(new_code).pretty())

test()


