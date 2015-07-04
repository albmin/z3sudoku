import z3


quest =  ( (7,None,None,9,None,None,None,None,None),
  (None,None,None,None,8,7,None,6,None),
  (None,8,9,None,1,None,None,None,2),
  (None,None,None,3,None,None,None,1,8),
  (4,None,None,None,None,None,None,None,7),
  (8,5,None,None,None,9,None,None,None),
  (6,None,None,None,3,None,4,8,None),
  (None,7,None,5,9,None,None,None,None),
  (None,None,None,None,None,6,None,None,3))


x = [list(i) for i in quest]

def solve_it(x):
	data = []
	counter = 1
	#preprocess the data into a new nested list
	for i in range(len(x)):
		data.append([])
		for j in range(len(x[i])):
			if x[i][j] == None:
				data[i].append(z3.Int(str(counter)+ 'a'))
				counter += 1
			else:
				data[i].append(z3.IntVal(j))
	#print data 

	solver = z3.Solver()
	
	#deal with the four constraints

	#uniqueness constraint for 3x3
	aa = []
	for i in data:
		aa.append()

	a = distinct_constraint()
	#uniqueness constraint for the column
	b = distinct_constraint()
	#uniqueness constraint for the row
	c = distinct_constraint()
	

def  distinct_constraint(y):
	return z3.Distinct(y)

#verify that the numbers are between the min and max
def range_constraint(y):
	return z3.And((1 <= x, x <= 9) for x in y)


solve_it(x)