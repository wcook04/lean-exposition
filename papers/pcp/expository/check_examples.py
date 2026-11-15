"""Exact finite examples; run with ordinary Python (without -O)."""
if not __debug__:
    raise SystemExit("Checks require ordinary Python without -O")

from itertools import product
from fractions import Fraction

def mul(a,b):
    out=0
    while b:
        if b&1: out ^= a
        b >>= 1; a <<= 1
        if a&16: a ^= 0b10011
    return out

def power(a,n):
    x=1
    for _ in range(n): x=mul(x,a)
    return x

def inv(a):
    assert a
    return power(a,14)

def addall(xs):
    x=0
    for y in xs: x ^= y
    return x

# GF(16), polynomial basis F2[t]/(t^4+t+1), primitive t=2.
assert [power(2,i) for i in range(15)] == [1,2,4,8,3,6,12,11,5,10,7,14,15,13,9]
nodes=[2,4,8]
weights=[mul(mul(nodes[(i+1)%3],nodes[(i+2)%3]), inv(mul(nodes[i]^nodes[(i+1)%3],nodes[i]^nodes[(i+2)%3]))) for i in range(3)]
assert weights == [12,5,8]
for coeff in product(range(16),repeat=3):
    f=lambda x: coeff[0]^mul(coeff[1],x)^mul(coeff[2],mul(x,x))
    assert f(0)==addall(mul(w,f(x)) for w,x in zip(weights,nodes))
f=lambda x: 3^mul(5,x)^mul(7,mul(x,x))
assert [f(x) for x in nodes]==[6,13,15]
assert addall(mul(w,f(x)) for w,x in zip(weights,nodes))==3
assert addall(f(x) for x in nodes)!=f(0)
old=power(2,5); assert power(old,3)==1 and old!=1
oldnodes=[power(old,i) for i in (1,2,3)]
frob=lambda x:power(x,4)
old_pass=sum(frob(u)==addall(frob(u^mul(a,v)) for a in oldnodes) for u,v in product(range(16),repeat=2))
new_pass=sum(frob(u)==addall(mul(w,frob(u^mul(a,v))) for a,w in zip(nodes,weights)) for u,v in product(range(16),repeat=2))
assert old_pass==256 and new_pass<256
assert not any(all(frob(x)==a^mul(b,x)^mul(c,mul(x,x)) for x in range(16)) for a,b,c in product(range(16),repeat=3))
print('GF16 nodes, weights, evaluations:',nodes,weights,[f(x) for x in nodes])
print('Frobenius x^4 checks: old',old_pass,'/ 256; corrected',new_pass,'/ 256; no quadratic representation')

# Three-bit Hadamard word and BLR test, uniform ordered a,b.
h=lambda x: (x&0b101).bit_count()%2
word=[h(x) for x in range(8)]
g=lambda x: h(x)^(x==1)
accepted=sum((g(a)^g(b))==g(a^b) for a,b in product(range(8),repeat=2))
correction=[sum((g(r)^g(r^x))==h(x) for r in range(8)) for x in range(8)]
assert word==[0,1,0,1,1,0,1,0] and accepted==46 and correction==[8,6,6,6,6,6,6,6]
assert all((h(a)^h(b))==h(a^b) for a,b in product(range(8),repeat=2))
print('Hadamard word:',word,'corrupt index 1; BLR acceptance',accepted,'/ 64; self-correction counts',correction,'/ 8')

# GF(5), H={0,1}; P=(x^2-x)(y+1)+(y^2-y)(x+2).
P=lambda x,y: ((x*x-x)*(y+1)+(y*y-y)*(x+2))%5
assert all(P(x,y)==0 for x,y in product((0,1),repeat=2))
assert P(2,2)==4 and P(2,0)==2
print('Grid H={0,1}: P at grid', [P(x,y) for x,y in product((0,1),repeat=2)], '; P(2,2)=',P(2,2),'; P(2,0)=',P(2,0))

# GF(4) as subfield of GF(16), omega=6 (order 3); characteristic two.
w=old; colours=[1,w,power(w,2)]
assert set(colours)=={1,6,7}
assert all(power(a,3)==1 for a in colours)
prop=lambda a,b: power(a^b,3)^1
matrix=[[prop(a,b) for b in colours] for a in colours]
assert matrix==[[1,0,0],[0,1,0],[0,0,1]]
assert [prop(1,6),prop(6,7),prop(7,1)]==[0,0,0]
assert [prop(1,1),prop(1,7),prop(7,1)]==[1,0,0]
print('GF4 colors:',colours,'edge residual matrix:',matrix)
print('triangle proper residuals [0,0,0]; improper [1,0,0]')

# Check the coordinate formula against multiplication in the subfield above.
def from_coordinates(a, b):
    return a ^ (w if b else 0)


for a, b, c, d in product(range(2), repeat=4):
    value = mul(from_coordinates(a, b), from_coordinates(c, d))
    constant = (a * c + b * d) % 2
    omega_coefficient = (a * d + b * c + b * d) % 2
    assert value == from_coordinates(constant, omega_coefficient)
for a, b in product(range(2), repeat=2):
    u = from_coordinates(a, b)
    assert mul(w, u) == from_coordinates(b, a ^ b)
    cubic_label = (1 + a + b + a * b) % 2
    assert (power(u, 3) ^ 1) == from_coordinates(cubic_label, 0)
print('GF4 coordinates: all 16 products, four products by omega, and four cubic-residual labels checked.')

# Independent repetitions, bound conditional on a fixed proof.
assert (Fraction(3,4)**3)==Fraction(27,64)
print('Toy repetition: (3/4)^3 =',Fraction(3,4)**3)
print('All checks passed.')
