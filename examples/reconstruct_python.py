from .python_parser import python_parser2, python_parser3

from lark import Lark
from lark.reconstruct import Reconstructor

def test():

    test_code = '''
print("Hello World!")
'''

    tree = python_parser3.parse(test_code)

    # print '@@', tree.pretty()
    # for x in tree.find_data('true'):
    #     x.data = 'false'
    #     # x.children[0].value = '"HAHA"'

    print(tree.pretty())

    new_code = Reconstructor(python_parser3).reconstruct(tree)
    print new_code

    print(python_parser3.parse(new_code).pretty())

test()


