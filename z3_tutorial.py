
#!/usr/bin/env python

from z3 import *

# Basic z3 usage
# Here is a simple function that, using z3, returns whether or not the input values are within the given constraints
# If the constraints are not satisfiable, it returns None

def answer1(minimum_value, maximum_value, input_values):
    minimum_value = z3.IntVal(minimum_value)
    maximum_value = z3.IntVal(maximum_value)
    input_values = map(z3.IntVal, input_values)

    solver = z3.Solver()
    solver.add(minimum_value <= maximum_value)
    if solver.check() == z3.unsat:
        return None

    constraints = [ z3.And(minimum_value <= x, x <= maximum_value) for x in input_values ]
    solver.add(constraints)
    return solver.check() == z3.sat

assert(answer1(0, 4, [1,2]) == True)
assert(answer1(0, 4, [1,5]) == False)
assert(answer1(0, -1, [1,5]) == None)

# Pretty much just showing the z3.Distinct function
# Here is a simple function that, using z3, returns whether or not the input values are distinct
def answer2(input_values):
    input_values = map(z3.IntVal, input_values)
    solver = z3.Solver()
    solver.add(z3.Distinct(input_values))
    return solver.check() == z3.sat

assert(answer2([1,2,3,4]) == True)
assert(answer2([1,2,3,1]) == False)

# Demonstating the z3 model and how to grab the value of an integer constant
# This function takes a minimum value, maximum value, and some number of input values
# It returns None if the minimum value is not less than the maximum value
# It returns False if the input values are not distinct or if any of the values are not within the constraints
# If returns True if it is not possible to add a single value while still maintaining the above constraints
# If it makes it this far, it returns the value that can be added
def answer3(minimum_value, maximum_value, input_values):
    minimum_value = z3.IntVal(minimum_value)
    maximum_value = z3.IntVal(maximum_value)
    input_values = map(z3.IntVal, input_values)

    solver = z3.Solver()
    solver.add(minimum_value <= maximum_value)
    if solver.check() == z3.unsat:
        return None

    # z3 does not like generators
    solver.add([z3.And(minimum_value <= x, x <= maximum_value) for x in input_values])
    solver.add(z3.Distinct(input_values))
    if solver.check() == z3.unsat:
        return False

    x = z3.Int('x')
    solver.add(z3.And(minimum_value <= x, x <= maximum_value))
    solver.add(z3.Distinct([x]+input_values))
    if solver.check() == z3.unsat:
        return True

    model = solver.model()
    return model.evaluate(x)


assert(answer1(0, 4, [1,2]) == True)
assert(answer1(0, 4, [1,5]) == False)
assert(answer1(0, -1, [1,5]) == None)
# Now use z3 to write a Sudoku solver
# Take the initial state as a list of lists

# Here is an example puzzle to solve:
# ( (7,None,None,9,None,None,None,None,None),
#   (None,None,None,None,8,7,None,6,None),
#   (None,8,9,None,1,None,None,None,2),
#   (None,None,None,3,None,None,None,1,8),
#   (4,None,None,None,None,None,None,None,7),
#   (8,5,None,None,None,9,None,None,None),
#   (6,None,None,None,3,None,4,8,None),
#   (None,7,None,5,9,None,None,None,None),
#   (None,None,None,None,None,6,None,None,3), )