
import z3

def solve(puzzle):
    assert(len(puzzle) == 9)
    assert(False not in [len(puzzle[i]) == 9 for i in xrange(len(puzzle)) ])

    solver = z3.Solver()
    matrix = []
    constraints = []
    for i in xrange(9):
        matrix.append([])
        for j in xrange(9):
            matrix[-1].append(z3.Int('%dx%d' % (i,j)))
            
            if puzzle[i][j] is not None:
                constraints.append(matrix[i][j] == puzzle[i][j])

            constraints.append(matrix[i][j] <= 9)
            constraints.append(1 <= matrix[i][j])

    for i in xrange(9):
        constraints.append(z3.Distinct(matrix[i]))
        constraints.append(z3.Distinct([matrix[j][i] for j in xrange(9)]))

    for x in xrange(0, 9, 3):
        for y in xrange(0, 9, 3):
            constraints.append(z3.Distinct([matrix[x+i][y+j] for i in xrange(3) for j in xrange(3)]))

    solver.add(constraints)
    if solver.check() == z3.unsat:
        print 'Given puzzle can not be solved'
        return

    model = solver.model()
    result = [[model.evaluate(matrix[j][i]) for i in xrange(9)] for j in xrange(9)]
    z3.print_matrix(result)

puzzle = ( (7,None,None,9,None,None,None,None,None),
           (None,None,None,None,8,7,None,6,None),
           (None,8,9,None,1,None,None,None,2),
           (None,None,None,3,None,None,None,1,8),
           (4,None,None,None,None,None,None,None,7),
           (8,5,None,None,None,9,None,None,None),
           (6,None,None,None,3,None,4,8,None),
           (None,7,None,5,9,None,None,None,None),
           (None,None,None,None,None,6,None,None,3), )

solve(puzzle)

