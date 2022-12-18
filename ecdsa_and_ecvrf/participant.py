from ecdsa.ecdsa import *
from Crypto.Random import random
from Crypto.Hash import keccak
from ecdsa.ellipticcurve import Point
from vrf import*
import time



G = generator_256
ORDER = G.order()
order_minus_one=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364140
INFINITY=Point(None,None,None)
suite_string=b"0x01"
H = generator_256



class Participant():

    def __init__(self,id,share_received, polynomial, polynomial2):
            self.id=id
            self.vrf=ECVRF()
            self.share_received=share_received
            self.polynomial=polynomial
            self.polynomial2=polynomial2
#functions for Generating phase:
    
    def commit_to_be_qualified(self,i):
            commit=G*self.polynomial[i]+H*self.polynomial2[i]
            return {"id":i,"commitment":commit}
            

    
    def commit_polynomial_coeff(self,poly_coeff):
            commit=[]
            for i in poly_coeff:
                commit.append(G*i)
            return commit
