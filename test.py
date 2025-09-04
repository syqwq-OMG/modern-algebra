a="ind|rank|trace|svd|eye|ones|orth|rows|cols|zeros|diag|rref|hstack|vstack|nullspace|eigen|dim|atan2|softmax|eig|sign|const"
for i in a.split('|'):
    print('#let {}=math.op("{}")'.format(i,i))