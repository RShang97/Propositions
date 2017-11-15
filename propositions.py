
from enum import Enum       # requires Python >= 3.4

'''
program that provides general suite of functions for representing and manipulating propositions
'''
#----------------------------
# reduce function. Takes an iterable and reduces it to one value by applying a function to all the items in the iterable
#----------------------------
def reduce(f, iterable, initializer=None):
    it = iter(iterable)
    if initializer is None:
        try:
            initializer = next(it)
        except IndexError:
            raise TypeError('reduce() of empty iterable with no initial value')
    accumulator = initializer
    for item in it:
        accumulator = f(accumulator, item)
    return accumulator

#----------------------------
# code for representing logical propositions. proposition is a class. with a function __repr__ that
# takes in a variable self and returns a representation of it after copmaring its types
#----------------------------
class Proposition:
    def __repr__(self):
        if isinstance(self, Var):
            return self.var
        elif isinstance(self, Neg):
            return '~' + repr(self.prop)
        elif isinstance(self, BinOp):
            return '( ' + repr(self.left) + ' ' + self.op.name + ' ' + repr(self.right) + ' )'
        else:
            return '<unrecognized instance of Proposition>'

    # functions that take a variable self and return the negative or inverted form of it
    def __neg__(self):
        return Neg(self)

    def __invert__(self): # A = binop(logop.or, Var('p') Neg(Var('q')))
        return Neg(self)

    '''
        eval: (Proposition, dict(str: bool)) -> bool
        evaluates this proposition by substituting variables for the given truth values
    '''
    def eval(self, truthValues): # truth values can be passed in as bools ; dictionary is key value mapping form is {'p': false etc. }

        # basecase, if it's a variable then you can evalute its truth value
        if isinstance(self, Var):
            return truthValues.get(str(self))
        # if it's a negative then return the invest. Check if neg is BINOP or VAR. if
        if isinstance(self, Neg):
            # if it's binop or neg, just call eval again. if it's a var, just invert it on the spot and return it
            if isinstance(self.prop, BinOp) or isinstance(self.prop, Neg):
                return not self.prop.eval(truthValues)
            elif isinstance(self.prop, Var):
                return not truthValues.get(str(self.prop))
        if isinstance(self, BinOp):
            if self.op == LogOp.OR:
                return self.left.eval(truthValues) or self.right.eval(truthValues)
            else:
                return self.left.eval(truthValues) and self.right.eval(truthValues)

# Var is a class made by taking a proposition and a string and sets self.var to the given var
class Var(Proposition):
    def __init__(self, var):
        if not isinstance(var, str): raise TypeError("variable must be a string")
        self.var = var

# takes a proposition and sets self.prop to that value?
class Neg(Proposition):
    def __init__(self, prop):
        if not isinstance(prop, Proposition): raise TypeError("only propositions can be negated")
        self.prop = prop
        
# class LogOp has instance varaibles And and OR
class LogOp(Enum):
    AND = 1
    OR = 2

class BinOp(Proposition):
    def __init__(self, op, left, right):
        if not isinstance(op, LogOp): raise TypeError("operation is invalid")
        if not isinstance(left, Proposition): raise TypeError("left operand is not a proposition")
        if not isinstance(right, Proposition): raise TypeError("right operand is not a proposition")
        self.op = op
        self.left = left
        self.right = right

#----------------------------
# convenience functions to build propositions with logical connectors
#----------------------------
'''
    conj: (Proposition, Proposition) -> Proposition
    returns a representation of p AND q
'''
def conj(p, q):
    return BinOp(LogOp.AND, p, q)

'''
    disj: (Proposition, Proposition) -> Proposition
    returns a representation of p OR q
'''
def disj(p, q):
    return BinOp(LogOp.OR, p, q)

'''
    cond: (Proposition, Proposition) -> Proposition
    returns a representation of p IMPLIES q
'''
def cond(p, q):
    # !p OR q
    return BinOp(LogOp.OR, Neg(p), q)# writes conditoinals

#----------------------------
# functions to process & evaluate arguments
#----------------------------
'''
    argument: (iterable of Proposition, Proposition) -> Proposition
    make a single proposition from all the premises and the conclusion
'''
def fromArgument(premises, conclusion):
    premises = reduce(conj, premises)
    return cond(premises, conclusion)


'''
    distributes the negative
    negNorm: Proposition -> Proposition

    return a negative-normal representation of the given proposition
    this is a form where negations are applied only to variables and not to more complex propositions
'''
def negNorm(prop): # distributes the negative
    if isinstance(prop, Var):
        return prop
    elif isinstance(prop, Neg):
        if isinstance(prop.prop, Neg):
            return prop.prop.prop
        elif isinstance(prop.prop, Var):
            return prop
        elif isinstance(prop.prop, BinOp):
            p = negNorm(Neg(prop.prop.left))
            q = negNorm(Neg(prop.prop.right))
            if prop.prop.op == LogOp.AND:
                operator = LogOp.OR
            else:
                operator = LogOp.AND
            prop = BinOp(operator, p, q)
            return prop
    elif isinstance(prop, BinOp):
        a = negNorm(prop.left)
        b = negNorm(prop.right)
        prop = BinOp(prop.op, a, b)
        return prop


'''
    toCNF: Proposition -> Proposition
    convert prop to conjunctive normal form
'''
def toCNF(prop): # for every varaible must have its oppositive once have cnf, split into or groupsings, check for opposites
    if isinstance(prop, Var) or isinstance(prop, Neg):
        return prop
    if isinstance(prop, BinOp):
        p = toCNF(prop.left)# call to cnf on
        q = toCNF(prop.right)
        if prop.op == LogOp.AND:
            return conj(p, q)
        elif prop.op == LogOp.OR:
            if not isinstance(p, Var) and not isinstance(p, Neg):
                if p.op == LogOp.AND:
                    prop = cleaver(p, q)
            if not isinstance(q, Var) and not isinstance(q, Neg):
                if q.op == LogOp.AND:
                    prop = cleaver(q, p)

            return prop

# takes a proposition and converts it to conjunctive normal form
def cleaver(anded, other):

# first thing it checks for is logical and. if there's an or then just give the proposition
# otherwise, the left matches the normal, just cleaver
    c = BinOp(LogOp.OR, anded.left, other)
    if isinstance(anded.left, BinOp):
        if anded.left.op == LogOp.AND:
            c = cleaver(anded.left, other)
    elif isinstance(other, BinOp):
        if isinstance(other, BinOp):
            c = cleaver(other, anded.left)
    d = BinOp(LogOp.OR, anded.right, other)
    if isinstance(anded.right, BinOp):
        if anded.right.op == LogOp.AND:
            d = cleaver(anded.right, other)
    elif isinstance(other, BinOp):
        if other.op == LogOp.AND:
            d = cleaver(other, anded.right)
    return conj(c, d)

def isValid(prop):
    # start by converting the proposition to a negative-normal CNF formula
    prop = toCNF(negNorm(prop))
    if not isinstance(prop, BinOp):
        return False
    else:
        if prop.op == LogOp.AND:
            return isValid(prop.left) and isValid(prop.right)
        elif prop.op == LogOp.OR:
            norm = set()
            opp = set()

            tautologer(prop.left, norm, opp)
            tautologer(prop.right, norm, opp)

            if len(norm.intersection(opp)) < 0:
                return False
            else:
                return True

def tautologer(disjunction, norm, opp):
    if isinstance(disjunction, Var):
        norm.add(disjunction)
    elif isinstance(disjunction, Neg):
        opp.add(disjunction.prop)
    else:
        tautologer(disjunction.left, norm, opp)
        tautologer(disjunction.right, norm, opp)

'''
    checkArgument: (iterable of Proposition, Proposition) -> bool
    returns whether or not an argument is valid
'''
def checkArgument(premises, conclusion):
    return isValid(fromArgument(premises, conclusion))

'''
    isSound: (iterable of Proposition, Proposition, dict(str: bool)) -> bool
    returns whether or not an argument is sound given truth values for variables
'''
def isSound(premises, conclusion, truthValues):
    return checkArgument(premises, conclusion) and reduce(lambda x, y: x and y.eval(truthValues), premises, True)

# various unit tests
def main():
    dictionary = {"r":False,"p":False,"q":False,"s":False}
    a = BinOp(LogOp.OR, Var('p'), Var('q'))
    b = BinOp(LogOp.AND, Var('r'), Var('s'))
    c = BinOp(LogOp.OR, a, b)

    print(c)
    c = toCNF(c)
    print(c)
    print(c.eval(dictionary))
    a = Var('a')
    b = Var('b')
    b = Neg(BinOp(LogOp.AND, b, a))
    c = Var('c')
    '''
    d = BinOp(LogOp.OR, c, b)
    print("ilias")
    print(d)
    d = negNorm(d)
    d = isValid(d)
    '''

    print(b)
    print(c.eval({"c": True}))
    print(b.eval({"a": True, "b": False}))
    '''
    p = Neg(conj(a, Neg(b)))
    q = Neg(disj(c, d))
    r = disj(p, q)
    print(r)
    r = negNorm(r)
    print(r)
    '''
    print("test negnorm")
    a = BinOp(LogOp.OR, Neg(Var('c')), Var('d'))
    print(a)
    a = negNorm(a)
    print(a)

    a = Neg(Var('a'))
    b = Var('a')
    c = disj(a, b)
    print(isValid(c))
    print(isValid(b))
    a = Var('a')
    b = Var('b')
    c = Var('c')
    d = Var('d')
    e = Var("e")
    f = Var("f")
    g = Neg(c)
    h = Neg(d)

    jeff = disj(a, b)
    dan = disj(e,f)

    jan = conj(jeff, dan)
    print(isValid(jan))
    a = conj(a, b)
    d = conj(e, f)

    c = conj(d, c)
    i = BinOp(LogOp.OR, a, c )
    print(i)
    i = toCNF(i)
    print(i)
if __name__ == '__main__':
    main()
