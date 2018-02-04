"This module implements an experimental Earley Parser with a dynamic lexer"

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
# Instead of running a lexer beforehand, or using a costy char-by-char method, this parser
# uses regular expressions by necessity, achieving high-performance while maintaining all of
# Earley's power in parsing any CFG.
#
#
# Author: Erez Shinan (2017)
# Email : erezshin@gmail.com

import collections

from ..common import ParseError, UnexpectedToken, is_terminal
from ..lexer import Token, UnexpectedInput
from ..tree import Tree
from .grammar_analysis import GrammarAnalyzer

from .earley import ApplyCallbacks, Item, Column

class Parser:
    def __init__(self,  parser_conf, term_matcher, resolve_ambiguity=None, ignore=(), predict_all=False):
        self.analysis = GrammarAnalyzer(parser_conf)
        self.parser_conf = parser_conf
        self.resolve_ambiguity = resolve_ambiguity
        self.ignore = list(ignore)
        self.predict_all = predict_all

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
        delayed_matches = collections.defaultdict(list)
        match = self.term_matcher

        text_line = 1
        text_column = 0

        def predict(nonterm, column):
            assert not is_terminal(nonterm), nonterm
            for rule in self.predictions[nonterm]:
                column.add(Item(rule, 0, column))

        def complete(item, column):
            name = item.rule.origin
            is_empty_item = item.start.i == column.i
            is_empty_rule = not self.FIRST[name]
            for key in list(item.start.to_predict):
                if item.start.to_predict[key].expect == name:
                    new_item = item.start.to_predict[key].advance()
                    if new_item == item:
                        raise ParseError('Infinite recursion detected! (rule %s)' % item.rule)

                    column.add(new_item)
                    new_item.add_derivation(item.start.i, column.i, item.tree)
                    if is_empty_rule:
                        del item.start.to_predict[key]

            # Special case for empty rules; which will always match.
            # Ensure we continue to advance any items that depend on them.
            if is_empty_rule:
                del column.to_reduce[item]

        def predict_and_complete(column):
            previous_to_predict = []
            previous_to_reduce = []
            while True:
                to_reduce = [i for i in column.to_reduce if i not in previous_to_reduce]
                previous_to_reduce = set(column.to_reduce.keys())

                to_predict = [i for i in column.to_predict if i not in previous_to_predict]
                previous_to_predict = set(column.to_predict.keys())

                if not (to_predict or to_reduce):
                    break

                for nonterm in to_predict:
                    if nonterm.ptr:
                        predict(nonterm.expect, column)

                for item in to_reduce:
                    complete(item, column)

        def scan(i, token, column):
            to_scan = set(column.to_scan)
            for x in self.ignore:
                m = match(x, stream, i)
                if m:
                    # Carry over any items currently in the scan buffer, to past
                    # the end of the ignored items.
                    delayed_matches[m.end()] += [(item, None) for item in to_scan]

                    # If we're ignoring up to the end of the file,
                    # carry over the start symbol if it already completed.
                    delayed_matches[m.end()] += [(item, None) for item in column.to_reduce if item.rule.origin == start_symbol]

                    # TODO add partial matches for ignore too?
                    # s = m.group(0)
                    # for j in range(1, len(s)):
                    #     m = x.match(s[:-j])
                    #     if m:
                    #         delayed_matches[m.end()] += to_scan

            for item in to_scan:
                m = match(item.expect, stream, i)
                if m:
                    t = Token(item.expect, m.group(0), i, text_line, text_column)
                    delayed_matches[m.end()].append((item.advance(), t))

                    s = m.group(0)
                    for j in range(1, len(s)):
                        m = match(item.expect, s[:-j])
                        if m:
                            t = Token(item.expect, m.group(0), i, text_line, text_column)
                            delayed_matches[i+m.end()].append((item.advance(), t))
#

            next_set = Column(i+1, self.FIRST, predict_all=self.predict_all)
            for item, t in delayed_matches[i+1]:
                assert isinstance(item, Item)
                next_set.add(item)
                if t is not None:
                    item.add_derivation(t.column, next_set.i, t)
            del delayed_matches[i+1]    # No longer needed, so unburden memory

            if not next_set and not delayed_matches:
                raise UnexpectedInput(stream, i, text_line, text_column, to_scan)

            return next_set

        # Main loop starts
        column0 = Column(0, self.FIRST, predict_all=self.predict_all)
        predict(start_symbol, column0)

        column = column0
        for i, token in enumerate(stream):
            predict_and_complete(column)
            column = scan(i, token, column)

            if token == '\n':
                text_line += 1
                text_column = 0
            else:
                text_column += 1

        predict_and_complete(column)

        # Parse ended. Now build a parse tree
        solutions = [n.tree for n in column.to_reduce.values()
                     if n.rule.origin==start_symbol and n.start is column0]

        if not solutions:
            expected_tokens = [t.expect for t in column.to_scan.values()]
            raise ParseError('Unexpected end of input! Expecting a terminal of: %s' % expected_tokens)

        elif len(solutions) == 1:
            tree = solutions[0]
        else:
            tree = Tree('_ambig', solutions)

        if self.resolve_ambiguity:
            tree = self.resolve_ambiguity(tree)

        return ApplyCallbacks(self.postprocess).transform(tree)


