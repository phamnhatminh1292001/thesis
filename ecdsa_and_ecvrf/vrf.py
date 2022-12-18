from ecdsa.ecdsa import *
from Crypto.Random import random
from Crypto.Hash import keccak
from ecdsa.ellipticcurve import Point
import time



G = generator_256
ORDER = G.order()
order_minus_one=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364140
INFINITY=Point(None,None,None)
suite_string=b"0x01"

def ECVRF_hash_to_curve_try_and_increment(pk, x, suite_string):
    #follow the ecvrf irtf draft
    ctr=0
    pk_string=str(pk).encode()
    one_string=int(0).to_bytes(1,'big')
    zero_string=int(1).to_bytes(1,'big')
    #because the == operation in the elliptic curve class only compare
    #two Points, we cannot use H=="INVALID" (can't compare a Point and a
    # string) but instead use H==INFINITY
    #because if H==INFINITY is also an invalid condition and it does not
    #change anything.
    H=INFINITY
    while  H==INFINITY:
        hash=keccak.new(digest_bits=256)
        ctr_string=str(ctr).encode()
        hash.update(suite_string)
        hash.update(one_string)
        hash.update(pk_string)
        hash.update(str(x).encode())
        hash.update(ctr_string)
        hash.update(zero_string)
        ctr+=1
        hash=hash.digest()
        H=string_to_curve(hash)
    return H


def string_to_curve(string):
    #specified in 2.3.4 of https://www.secg.org/sec1-v2.pdf
    #since the curve is secp256k1, then q=p is an odd prime
    #we want to implement for secp256k1 therefore we will just implement step 1, 
    # 2.2 and 2.4.1
    #Step 1
    if string==int(2).to_bytes(1,'big'):
        return INFINITY
    #Step 2.2
    x=string_to_field(string)
    if x=="INVALID":
        return INFINITY
    p=secp256k1._CurveFp__p
    #Step 2.4.1
    # let t=x^3+7 (mod p) 
    t=(pow(x,3,p)+secp256k1._CurveFp__a*x+secp256k1._CurveFp__b)%p
    QR=pow(t,(p-1)//2,p)
    if QR==(p-1):
        return INFINITY
    # because p=3 (mod 4), we see that y=t^((p+1)/4)
    beta=pow(t,(p+1)//4,p)
    if beta%2==0:
        return Point(secp256k1,x,beta)
    else:
        return Point(secp256k1,x,p-beta)
    

def string_to_field(string): 
    #specified in 2.3.6 of https://www.secg.org/sec1-v2.pdf
    #since i just want to implement for secp256k1, i will just implement step 1
    #in fact, step 1 is just the function string_to_integer in part 2.3.8 of the
    #same paper
    x=0
    for i in range (0,len(string)):
        x+=pow(256,len(string)-1-i)*int(hex(string[i]),16)
    if x<secp256k1._CurveFp__p:
        return x
    return "INVALID"


def ECVRF_hash_points(point_list):
        # based on the irtf internet draft
        #we use the keccak instead of sha256
        hash = keccak.new(digest_bits=256)
        for i in point_list:
            hash.update(str(i).encode())
        return int(hash.hexdigest(), 16) % ORDER

 
class ECVRF():

    def __init__(self):
            self.sk = random.randint(0,order_minus_one)
            self.pk = G*self.sk 
    
    def prove(self, x, sk):
        # the evaluation function, based on the paper [PWHVNRG17]
        # step 1 compute h
        H = ECVRF_hash_to_curve_try_and_increment(self.pk,x,suite_string)
        #step 2 let gamma=h^sk
        gamma = H*sk
        #step 3 choose a random k
        k = random.randint(0,order_minus_one)
        #step 4 compute c=Hash_point(g,h,g^sk,h^sk,g^k,h^k)
        point_list=[G, H, self.pk, gamma, G*k, H*k]
        c = ECVRF_hash_points(point_list)
        #step 5 compute s=k-c*sk (mod order)
        s = (k - c*sk)% ORDER
        # the proof consists of gamma, c and s
        pi = {'gamma': gamma, 'c': c,  's': s}
        # the output is the keccak hash of gamma
        y = gamma
        return {'output': y, 'proof': pi, 'public key': self.pk}
    
    def verify(self, x, y, pi, pk):
        # this function, given an input x, a value y, a proof pi and 
        # the public key pk,
        # verify if the output y was calculated correctly from x
        gamma = pi['gamma']
        c = pi['c']
        s = pi['s']
        #step 1 compute U=c*pk+G*s
        U = c*pk + G*s
        #step 2 compute V=c*gamma+H*s
        H = ECVRF_hash_to_curve_try_and_increment(pk,x,suite_string)
        #step 3 compute V=c*gamma+h*s
        V = c*gamma + H*s
        point_list=[G,H,pk,gamma,U,V]
        #calculate the value Hash_point(G,H,pk,gamma,U,V)
        c2 = ECVRF_hash_points(point_list)
        #calculate the keccak hash of gamma
        hash = keccak.new(digest_bits=256)
        hash.update(str(gamma).encode())
        #step 4 check if c=Hash_point(g,h,pk,gamma,u,v) and y=keccak(gamma)
        return c == c2 and y == gamma




vrf=ECVRF()
prov=vrf.prove(999,vrf.sk)
pi=prov["proof"]
y=prov["output"]
public_key=prov["public key"]


verify=vrf.verify(999,y,pi,public_key)
print(verify)




#ecdsa=ECDSA()
#sign=ecdsa.sign(alpha)
#r=sign['r']
#s=sign['s']
#pk=sign['pk']
#start_time = time.time()
#verify=ecdsa.verify(alpha,r,s,pk)
#end_time = time.time()
#elapsed_time = end_time - start_time
#print ("elapsed_time:{0}".format(elapsed_time) + "[sec]")

