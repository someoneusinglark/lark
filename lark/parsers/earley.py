"This module implements an Earley Parser"

# The parser uses a parse-forest to keep track of derivations and ambiguations.
# When the parse ends successfully, a disambiguation stage resolves all ambiguity
# (right now ambiguity resolution is not developed beyond the needs of lark)
# Afterwards the parse tree is reduced (transformed) according to user callbacks.
# I use the no-recursion version of Transformer and Visitor, because the tree might be
# deeper than Python's recursion limit (a bit absurd, but that's life)
#
# The algorithm keeps track of each state set, using a corresponding Column instance.
# Column keeps track of new items using NewsList instances.
#
# Author: Erez Shinan (2017)
# Email : erezshin@gmail.com

from ..common import ParseError, UnexpectedToken, is_terminal
from ..tree import Tree, Visitor_NoRecurse, Transformer_NoRecurse
from ..lexer import Token
from ..grammar import Rule
from .grammar_analysis import GrammarAnalyzer

import collections

class DerivationList(collections.Container):
    def __init__(self, tree = None):
        assert isinstance(tree, DerivationList) or tree is None
        self.tree = dict(tree.tree) if tree is not None else {}

    def __contains__(self, key):
        assert(len(key) == 2)
        assert(isinstance(key[0], int) and isinstance(key[1], int))
        if key in self.tree:
            return True
        return False

    def __len__(self):
        return len(self.tree)

    def __setitem__(self, key, value):
        if isinstance(key, tuple):
            assert(len(key) == 3)
            assert(isinstance(key[0], int) and isinstance(key[1], int) and isinstance(key[2], int))
            if key in self.tree:
                current = self.tree[key]
                if isinstance(current, Tree) and current.data == '_ambig' and value not in current.children:
                    current.children.append(value)
                    return
                elif current != value:
                    ambiguous = Tree('_ambig', [current, value])
                    self.tree[key] = ambiguous
                    return
            else:
                self.tree[key] = value
        else:
            raise KeyError('invalid key {}'.format(key))

    def __getitem__(self, key):
        if isinstance(key, int):
            i = 0
            for value in iter(self):
                if i == key:
                    return value
                i = i + 1

        elif isinstance(key, tuple):
            assert(len(key) == 3)
            assert(isinstance(key[0], int) and isinstance(key[1], int) and isinstance(key[2], int))
            return self.tree[key]
        else:
            raise KeyError('invalid key {}'.format(key))

    def __iter__(self):
        for i in sorted(self.tree):
            yield self.tree[i]

    def __hash__(self):
        return hash(tuple(self.tree))

#    def __repr__(self):
#        printer = pprint.PrettyPrinter(indent=4, width=80, depth=3)
#        return "{}".format(printer.pformat(self.tree))

class Derivation(Tree):
    def __init__(self, rule, children=None):
        assert isinstance(rule, Rule)
        Tree.__init__(self, 'drv', DerivationList(children) if children is not None else DerivationList())
        self.rule = rule

    def add(self, start_idx, end_idx, ptr, value):
        self.children[start_idx, end_idx, ptr] = value

    def __repr__(self):
        return 'Derivation(%s, %s, %s)' % (self.rule, self.data, self.children)

    def __hash__(self):
        return hash((self.data, tuple(self.children)))

class Item(object):
    "An Earley Item, the atom of the algorithm."

    def __init__(self, rule, ptr, start, tree = None):
        assert isinstance(rule, Rule)
        self.rule = rule
        self.ptr = ptr
        self.start = start
        self.tree = tree if tree is not None else Derivation(self.rule)

    @property
    def expect(self):
        return self.rule.expansion[self.ptr]

    @property
    def is_complete(self):
        return self.ptr == len(self.rule.expansion)

    def add_derivation(self, start_idx, end_idx, item):
        self.tree.add(start_idx, end_idx, self.ptr, item)

    def advance(self):
        assert self.tree.data == 'drv'
        new_tree = Derivation(self.rule, self.tree.children)
        return self.__class__(self.rule, self.ptr+1, self.start, new_tree)

    def __eq__(self, other):
        return self.start is other.start and self.ptr == other.ptr and self.rule == other.rule

    def __hash__(self):
        return hash((self.rule, self.ptr, id(self.start)))   # Always runs Derivation.__hash__

    def __repr__(self):
        before = list(map(str, self.rule.expansion[:self.ptr]))
        after = list(map(str, self.rule.expansion[self.ptr:]))
        return '<(%d) (%d) %s : %s * %s>' % (id(self), id(self.start), self.rule.origin, ' '.join(before), ' '.join(after))

class Column:
    "An entry in the table, aka Earley Chart. Contains lists of items."
    def __init__(self, i, FIRST, predict_all=False):
        self.i = i

        ### Need to preserve insertion order for determism of the SPPF tree.
        self.to_reduce = collections.OrderedDict()
        self.to_predict = collections.OrderedDict()
        self.to_scan = collections.OrderedDict()
        self.item_count = 0
        self.FIRST = FIRST

        self.predict_all = predict_all

    def add(self, item):
        """Sort items into scan/predict/reduce newslists

        Makes sure only unique items are added.
        """
        if item.is_complete:
            item_hash = hash((item))
            return self.to_reduce.setdefault(item_hash, item)
        else:
            item_hash = hash((item))
            if is_terminal(item.expect):
                return self.to_scan.setdefault(item_hash, item)
            else:
                return self.to_predict.setdefault(item_hash, item)

    def __bool__(self):
        return bool(self.to_reduce or self.to_scan or self.to_predict)
    __nonzero__ = __bool__  # Py2 backwards-compatibility

class Parser:
    def __init__(self, parser_conf, term_matcher, resolve_ambiguity=None):
        self.analysis = GrammarAnalyzer(parser_conf)
        self.parser_conf = parser_conf
        self.resolve_ambiguity = resolve_ambiguity

        self.FIRST = self.analysis.FIRST
        self.postprocess = {}
        self.predictions = {}
        for rule in parser_conf.rules:
            self.postprocess[rule] = getattr(parser_conf.callback, rule.alias)
            self.predictions[rule.origin] = [x.rule for x in self.analysis.expand_rule(rule.origin)]

        self.term_matcher = term_matcher


    def parse(self, stream, start_symbol=None):
        # Define parser functions
        start_symbol = start_symbol or self.parser_conf.start

        _Item = Item
        match = self.term_matcher

        def predict(nonterm, column):
            assert not is_terminal(nonterm), nonterm
            for rule in self.predictions[nonterm]:
                new_item = column.add(_Item(rule, 0, column))
                column.add(new_item)

        def complete(item, column):
            name = item.rule.origin
            is_empty_rule = not self.FIRST[item.rule.origin]
            is_empty_item = item.start.i == column.i

            for key in list(item.start.to_predict.keys()):
                if item.start.to_predict[key].expect == name:
                    new_item = item.start.to_predict[key].advance()
                    if new_item == item:
                        raise ParseError('Infinite recursion detected! (rule %s)' % item.rule)

                    new_item = column.add(new_item)
                    new_item.add_derivation(item.start.i, column.i, item.tree)

                    ### Better would be: if not item.can_match_more del item.start.to_predict[key]
                    if is_empty_rule:
                        del item.start.to_predict[key]

            ### Posibbly better - if not item.rule.origin == start_symbol, del column.to_reduce[hash(item)]?
            if is_empty_rule:
                del column.to_reduce[hash(item)]

        def predict_and_complete(column):
            previous_to_predict = set([])
            previous_to_reduce = set([])
            while True:
                to_reduce = collections.OrderedDict(column.to_reduce)
                list(map(to_reduce.__delitem__, filter(to_reduce.__contains__, previous_to_reduce)))
                previous_to_reduce = set(column.to_reduce.keys())
                completed = to_reduce.values()

                to_predict = collections.OrderedDict(column.to_predict)
                list(map(to_predict.__delitem__, filter(to_predict.__contains__, previous_to_predict)))
                previous_to_predict = set(column.to_predict.keys())
                nonterms = [ nonterm.expect for nonterm in to_predict.values() if nonterm.ptr ]
    
                if not (to_predict or to_reduce):
                    break

                for nonterm in nonterms:
                    predict(nonterm, column)

                for item in completed:
                    complete(item, column)

        def scan(i, token, column):
            next_set = Column(i+1, self.FIRST)
            for item in column.to_scan.values():
                if match(item.expect, token):
                    new_item = next_set.add(item.advance())
                    new_item.add_derivation(column.i, next_set.i, token)

            if not next_set:
                expect = {i.expect for i in column.to_scan.values()}
                raise UnexpectedToken(token, expect, stream, i)

            return next_set

        # Main loop starts
        column0 = Column(0, self.FIRST)
        predict(start_symbol, column0)

        column = column0
        for i, token in enumerate(stream):
            predict_and_complete(column)
            column = scan(i, token, column)

        predict_and_complete(column)

        # Parse ended. Now build a parse tree
        solutions = [n.tree for n in column.to_reduce.values()
                     if n.rule.origin==start_symbol and n.start is column0]
        if not solutions:
            raise ParseError('Incomplete parse: Could not find a solution to input')
        elif len(solutions) == 1:
            tree = solutions[0]
        else:
            tree = Tree('_ambig', solutions)

        if self.resolve_ambiguity:
            tree = self.resolve_ambiguity(tree)

        return ApplyCallbacks(self.postprocess).transform(tree)


class ApplyCallbacks(Transformer_NoRecurse):
    def __init__(self, postprocess):
        self.postprocess = postprocess

    def drv(self, tree):
        children = tree.children
        callback = self.postprocess[tree.rule]
        if callback:
            return callback(children)
        else:
            return Tree(tree.rule, children)
