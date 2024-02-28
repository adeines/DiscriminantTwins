# Alex Barrios' code from explicit_isogenies/models.sage on github
# https://github.com/alexanderbarrios/explicit_isogenies/blob/main/models.sage

# 3-isogenous curves where both have j-invariant 0
def calE1_0(d):
    return EllipticCurve([0, d])
def calE2_0(d):
    return EllipticCurve([0, -27*d])

# 2-isogenous curves where both have j-invariant 1728
def calE1_1728(d):
    return EllipticCurve([d, 0])
def calE2_1728(d):
    return EllipticCurve([-4*d, 0])


# The Fricke parameterization for X_0(n)
P.<t> = QQ[]
j2_1(t) = (t+256)^3/t^2
j2_2(t) = (t+16)^3/t
j3_1(t) = (t+27)*(t+243)^3/t^3
j3_2(t) = (t+27)*(t+3)^3/t
j4_1(t) = (t^2+256*t+4096)^3/(t^4*(t+16))
j4_2(t) = (t^2+16*t+16)^3/(t*(t+16))
j5_1(t) = (t^2+250*t+3125)^3/t^5
j5_2(t) = (t^2+10*t+5)^3/t
j6_1(t) = (t+12)^3*(t^3+252*t^2+3888*t+15552)^3/(t^6*(t+8)^2*(t+9)^3)
j6_2(t) = (t+6)^3*(t^3+18*t^2+84*t+24)^3/(t*(t+8)^3*(t+9)^2)
j7_1(t) = (t^2+13*t+49)*(t^2+245*t+2401)^3/t^7
j7_2(t) = (t^2+13*t+49)*(t^2+5*t+1)^3/t
j8_1(t) = (t^4 + 240*t^3 +2144*t^2 +3840*t+256)^3/((t-4)^8*t*(t+4)^2)
j8_2(t) = (t^4 - 16*t^2+16)^3/((t^2-16)*t^2)
j9_1(t) = (t+6)^3*(t^3+234*t^2+756*t+2160)^3/((t-3)^8*(t^3-27))
j9_2(t) = t^3*(t^3-24)^3/(t^3-27)
j10_1(t) = (t^6+236*t^5+1440*t^4+1920*t^3+3840*t^2+256*t+256)^3/(t^2*(t-4)^10*(t+1)^5)
j10_2(t) = (t^6-4*t^5+16*t+16)^3/(t^5*(t-4)*(t+1)^2)
j12_1(t) = (t^2+6*t-3)^3*(t^6+234*t^5+747*t^4+540*t^3-729*t^2-486*t-243)^3/((t-3)^12*(t-1)*t^3*(t+1)^4*(t+3)^3)
j12_2(t) = (t^2-3)^3*(t^6-9*t^4+3*t^2-3)^3/(t^4*(t^2-9)*(t^2-1)^3)
j13_1(t) = (t^2+5*t+13)*(t^4+247*t^3+3380*t^2+15379*t+28561)^3/t^13
j13_2(t) = (t^2+5*t+13)*(t^4+7*t^3+20*t^2+19*t+1)^3/t
j16_1(t) = (t^8+240*t^7+2160*t^6+6720*t^5+17504*t^4+26880*t^3+34560*t^2+15360*t+256)^3/((t-2)^16*t*(t+2)^4*(t^2+4))
j16_2(t) = (t^8-16*t^4+16)^3/(t^4*(t^4-16))
j18_1(t) = (t^3+6*t^2+4)^3*(t^9+234*t^8+756*t^7+2172*t^6+1872*t^5+3024*t^4+48*t^3+3744*t^2+64)^3/((t-2)^18*t^2*(t+1)^9*(t^2-t+1)*(t^2+2*t+4)^2)
j18_2(t) = (t^3-2)^3*(t^9-6*t^6-12*t^3-8)^3/(t^9*(t^3-8)*(t^3+1)^2)
j25_1(t) = (t - 1)^-25 * (t^4 + t^3 + 6*t^2 + 6*t + 11)^-1 * (t^10 + 240*t^9 + 2170*t^8 + 8880*t^7 + 34835*t^6 + 83748*t^5 + 206210*t^4 + 313380*t^3 + 503545*t^2 + 424740*t + 375376)^3
j25_2(t) = (t^10+10*t^8+35*t^6-12*t^5+50*t^4-60*t^3+25*t^2-60*t+16)^3/(t^5+5*t^3+5*t-11)

# The Models \mathcal{C}_{n,i}(t,d)

def calC2_1(t,d):
    A=(-27) * (t + 64) * (t + 256) * d^2
    B=(-54) * (t - 512) * (t + 64)^2 * d^3
    return EllipticCurve([A,B])

def calC2_2(t,d):
    A=(-432) * (t + 16) * (t + 64) * d^2
    B=(-3456) * (t - 8) * (t + 64)^2 * d^3
    return EllipticCurve([A,B])

def calC3_1(t,d):
    A=(-3) * (t + 243) * d^2 * (t + 27)^3
    B=(-2) * d^3 * (t + 27)^4 * (t^2 - 486*t - 19683)
    return EllipticCurve([A,B])

def calC3_2(t,d):
    A=(-243) * (t + 3) * d^2 * (t + 27)^3
    B=(-1458) * d^3 * (t + 27)^4 * (t^2 + 18*t - 27)
    return EllipticCurve([A,B])

def calC4_1(t,d):
    A=(-432) * d^2 * (t^2 + 16*t + 256)
    B=(3456) * (t - 16) * (t + 8) * (t + 32) * d^3
    return EllipticCurve([A,B])

def calC4_2(t,d):
    A=(-6912) * d^2 * (t^2 + 16*t + 16)
    B=(221184) * (t + 8) * d^3 * (t^2 + 16*t - 8)
    return EllipticCurve([A,B])

def calC4_3(t,d):
    A=(-432) * d^2 * (t^2 - 224*t + 256)
    B=(3456) * (t - 16) * d^3 * (t^2 + 544*t + 256)
    return EllipticCurve([A,B])

def calC4_4(t,d):
    A=(-27) * d^2 * (t^2 + 256*t + 4096)
    B=(54) * (t + 32) * d^3 * (t^2 - 512*t - 8192)
    return EllipticCurve([A,B])

def calC5_1(t,d):
    A=(-27) * d^2 * (t^2 + 22*t + 125) * (t^2 + 250*t + 3125)
    B=(-54) * d^3 * (t^2 - 500*t - 15625) * (t^2 + 22*t + 125)^2
    return EllipticCurve([A,B])

def calC5_2(t,d):
    A=(-16875) * d^2 * (t^2 + 10*t + 5) * (t^2 + 22*t + 125)
    B=(-843750) * d^3 * (t^2 + 4*t - 1) * (t^2 + 22*t + 125)^2
    return EllipticCurve([A,B])

def calC6_1(t,d):
    A=(-3) * (t + 12) * d^2 * (t^3 + 252*t^2 + 3888*t + 15552)
    B=(-2) * d^3 * (t^2 + 36*t + 216) * (t^4 - 504*t^3 - 13824*t^2 - 124416*t - 373248)
    return EllipticCurve([A,B])

def calC6_2(t,d):
    A=(-48) * (t + 6) * d^2 * (t^3 + 18*t^2 + 324*t + 1944)
    B=(-128) * d^3 * (t^2 + 36*t + 216) * (t^4 - 216*t^2 - 1944*t - 5832)
    return EllipticCurve([A,B])

def calC6_3(t,d):
    A=(-243) * (t + 12) * d^2 * (t^3 + 12*t^2 + 48*t + 192)
    B=(-1458) * d^3 * (t^2 + 12*t + 24) * (t^4 + 24*t^3 + 192*t^2 - 4608)
    return EllipticCurve([A,B])

def calC6_4(t,d):
    A=(-3888) * (t + 6) * d^2 * (t^3 + 18*t^2 + 84*t + 24)
    B=(-93312) * d^3 * (t^2 + 12*t + 24) * (t^4 + 24*t^3 + 192*t^2 + 504*t - 72)
    return EllipticCurve([A,B])

def calC7_1(t,d):
    A=(-27) * d^2 * (t^2 + 13*t + 49) * (t^2 + 245*t + 2401)
    B=(-54) * d^3 * (t^2 + 13*t + 49) * (t^4 - 490*t^3 - 21609*t^2 - 235298*t - 823543)
    return EllipticCurve([A,B])

def calC7_2(t,d):
    A=(-64827) * d^2 * (t^2 + 5*t + 1) * (t^2 + 13*t + 49)
    B=(-6353046) * d^3 * (t^2 + 13*t + 49) * (t^4 + 14*t^3 + 63*t^2 + 70*t - 7)
    return EllipticCurve([A,B])

def calC8_1(t,d):
    A=(-432) * d^2 * (t^4 + 224*t^2 + 256)
    B=(-3456) * d^3 * (t^2 + 16) * (t^2 - 24*t + 16) * (t^2 + 24*t + 16)
    return EllipticCurve([A,B])

def calC8_2(t,d):
    A=(-432) * d^2 * (t^4 - 240*t^3 + 2144*t^2 - 3840*t + 256)
    B=(-3456) * d^3 * (t^2 - 24*t + 16) * (t^4 + 528*t^3 - 4000*t^2 + 8448*t + 256)
    return EllipticCurve([A,B])

def calC8_3(t,d):
    A=(-27) * d^2 * (t^4 + 240*t^3 + 2144*t^2 + 3840*t + 256)
    B=(-54) * d^3 * (t^2 + 24*t + 16) * (t^4 - 528*t^3 - 4000*t^2 - 8448*t + 256)
    return EllipticCurve([A,B])

def calC8_4(t,d):
    A=(-6912) * d^2 * (t^4 - 16*t^2 + 256)
    B=(-221184) * d^3 * (t^2 - 32) * (t^2 - 8) * (t^2 + 16)
    return EllipticCurve([A,B])

def calC8_5(t,d):
    A=(-6912) * d^2 * (t^4 - 256*t^2 + 4096)
    B=(-221184) * d^3 * (t^2 - 32) * (t^4 + 512*t^2 - 8192)
    return EllipticCurve([A,B])

def calC8_6(t,d):
    A=(-110592) * d^2 * (t^4 - 16*t^2 + 16)
    B=(-14155776) * d^3 * (t^2 - 8) * (t^4 - 16*t^2 - 8)
    return EllipticCurve([A,B])

def calC9_1(t,d):
    A=(-3) * (t + 6) * d^2 * (t^3 + 234*t^2 + 756*t + 2160)
    B=(-2) * d^3 * (t^6 - 504*t^5 - 16632*t^4 - 123012*t^3 - 517104*t^2 - 1143072*t - 1475496)
    return EllipticCurve([A,B])

def calC9_2(t,d):
    A=(-243) * t * (t + 6) * d^2 * (t^2 - 6*t + 36)
    B=(-1458) * d^3 * (t^2 - 6*t - 18) * (t^4 + 6*t^3 + 54*t^2 - 108*t + 324)
    return EllipticCurve([A,B])

def calC9_3(t,d):
    A=(-19683) * t * d^2 * (t^3 - 24)
    B=(-1062882) * d^3 * (t^6 - 36*t^3 + 216)
    return EllipticCurve([A,B])

def calC10_1(t,d):
    A=(-27) * d^2 * (t^2 + 4) * (t^6 + 236*t^5 + 1440*t^4 + 1920*t^3 + 3840*t^2 + 256*t + 256)
    B=(-54) * d^3 * (t^2 + 4*t + 8) * (t^2 + 22*t - 4) * (t^2 + 4)^2 * (t^4 - 536*t^3 - 264*t^2 - 416*t - 64)
    return EllipticCurve([A,B])

def calC10_2(t,d):
    A=(-432) * d^2 * (t^2 + 4) * (t^6 - 4*t^5 + 240*t^4 - 480*t^3 + 1440*t^2 - 944*t + 16)
    B=(-3456) * d^3 * (t^2 - 2*t + 2) * (t^2 + 22*t - 4) * (t^2 + 4)^2 * (t^4 - 26*t^3 + 66*t^2 - 536*t - 4)
    return EllipticCurve([A,B])

def calC10_3(t,d):
    A=(-16875) * d^2 * (t^2 + 4) * (t^6 - 4*t^5 + 256*t + 256)
    B=(-843750) * d^3 * (t^2 - 2*t - 4) * (t^2 + 4*t + 8) * (t^2 + 4)^2 * (t^4 - 8*t^3 + 24*t^2 - 32*t - 64)
    return EllipticCurve([A,B])

def calC10_4(t,d):
    A=(-270000) * d^2 * (t^2 + 4) * (t^6 - 4*t^5 + 16*t + 16)
    B=(-54000000) * d^3 * (t^2 - 2*t - 4) * (t^2 - 2*t + 2) * (t^2 + 4)^2 * (t^4 - 2*t^3 - 6*t^2 - 8*t - 4)
    return EllipticCurve([A,B])

def calC11_1(d):
    A=(-395307) * d^2
    B=(373960422) * d^3
    return EllipticCurve([A,B])

def calC11_2(d):
    A=(-38907) * d^2
    B=(-2953962)  * d^3
    return EllipticCurve([A,B])

def calC11_3(d):
    A=(-1149984) * d^2
    B=(-487018224) * d^3
    return EllipticCurve([A,B])

def calC11_4(d):
    A=(-9504) * d^2
    B=(365904) * d^3
    return EllipticCurve([A,B])

def calC12_1(t,d):
    A=(-48) * d^2 * (t^2 + 3) * (t^6 + 225*t^4 - 405*t^2 + 243)
    B=(-128) * d^3 * (t^4 + 18*t^2 - 27) * (t^4 - 24*t^3 + 18*t^2 - 27) * (t^4 + 24*t^3 + 18*t^2 - 27)
    return EllipticCurve([A,B])

def calC12_2(t,d):
    A=(-3888) * d^2 * (t^2 + 3) * (t^6 - 15*t^4 + 75*t^2 + 3)
    B=(-93312) * d^3 * (t^4 - 6*t^2 - 3) * (t^4 - 6*t^2 - 24*t - 3) * (t^4 - 6*t^2 + 24*t - 3)
    return EllipticCurve([A,B])

def calC12_3(t,d):
    A=(-768) * d^2 * (t^2 - 3) * (t^6 - 9*t^4 + 243*t^2 - 243)
    B=(-8192) * d^3 * (t^4 + 18*t^2 - 27) * (t^8 - 36*t^6 + 270*t^4 - 972*t^2 + 729)
    return EllipticCurve([A,B])

def calC12_4(t,d):
    A=(-62208) * d^2 * (t^2 - 3) * (t^6 - 9*t^4 + 3*t^2 - 3)
    B=(-5971968) * d^3 * (t^4 - 6*t^2 - 3) * (t^8 - 12*t^6 + 30*t^4 - 36*t^2 + 9)
    return EllipticCurve([A,B])

def calC12_5(t,d):
    A=(-3) * d^2 * (t^2 + 6*t - 3) * (t^6 + 234*t^5 + 747*t^4 + 540*t^3 - 729*t^2 - 486*t - 243)
    B=(-2) * d^3 * (t^4 + 24*t^3 + 18*t^2 - 27) * (t^8 - 528*t^7 - 3996*t^6 - 9504*t^5 + 270*t^4 + 14256*t^3 - 972*t^2 + 729)
    return EllipticCurve([A,B])

def calC12_6(t,d):
    A=(-243) * d^2 * (t^2 + 6*t - 3) * (t^6 - 6*t^5 + 27*t^4 + 60*t^3 - 249*t^2 + 234*t - 3)
    B=(-1458) * d^3 * (t^4 - 6*t^2 + 24*t - 3) * (t^8 - 12*t^6 - 528*t^5 + 30*t^4 + 3168*t^3 - 3996*t^2 + 1584*t + 9)
    return EllipticCurve([A,B])

def calC12_7(t,d):
    A=(-48) * d^2 * (t^2 - 6*t - 3) * (t^6 - 234*t^5 + 747*t^4 - 540*t^3 - 729*t^2 + 486*t - 243)
    B=(-128) * d^3 * (t^4 - 24*t^3 + 18*t^2 - 27) * (t^8 + 528*t^7 - 3996*t^6 + 9504*t^5 + 270*t^4 - 14256*t^3 - 972*t^2 + 729)
    return EllipticCurve([A,B])

def calC12_8(t,d):
    A=(-3888) * d^2 * (t^2 - 6*t - 3) * (t^6 + 6*t^5 + 27*t^4 - 60*t^3 - 249*t^2 - 234*t - 3)
    B=(-93312) * d^3 * (t^4 - 6*t^2 - 24*t - 3) * (t^8 - 12*t^6 + 528*t^5 + 30*t^4 - 3168*t^3 - 3996*t^2 - 1584*t + 9)
    return EllipticCurve([A,B])

def calC13_1(t,d):
    A=(-27) * d^2 * (t^2 + 5*t + 13) * (t^2 + 6*t + 13) * (t^4 + 247*t^3 + 3380*t^2 + 15379*t + 28561)
    B=(-54) * d^3 * (t^2 + 5*t + 13) * (t^2 + 6*t + 13)^2 * (t^6 - 494*t^5 - 20618*t^4 - 237276*t^3 - 1313806*t^2 - 3712930*t - 4826809)
    return EllipticCurve([A,B])

def calC13_2(t,d):
    A=(-771147) * d^2 * (t^2 + 5*t + 13) * (t^2 + 6*t + 13) * (t^4 + 7*t^3 + 20*t^2 + 19*t + 1)
    B=(-260647686) * d^3 * (t^2 + 5*t + 13) * (t^2 + 6*t + 13)^2 * (t^6 + 10*t^5 + 46*t^4 + 108*t^3 + 122*t^2 + 38*t - 1)
    return EllipticCurve([A,B])

def calC14_1(d):
    A=(-2361555) * d^2
    B=(1396762542) * d^3
    return EllipticCurve([A,B])

def calC14_2(d):
    A=(-138915) * d^2
    B=(24504606) * d^3
    return EllipticCurve([A,B])

def calC14_3(d):
    A=(-48195) * d^2
    B=(-4072194) * d^3
    return EllipticCurve([A,B])

def calC14_4(d):
    A=(-2835) * d^2
    B=(-71442) * d^3
    return EllipticCurve([A,B])

def calC15_1(d):
    A=(-162675) * d^2
    B=(-25254450) * d^3
    return EllipticCurve([A,B])

def calC15_2(d):
    A=(-675) * d^2
    B=(-79650) * d^3
    return EllipticCurve([A,B])

def calC15_3(d):
    A=(712125) * d^2
    B=(-104861250) * d^3
    return EllipticCurve([A,B])

def calC15_4(d):
    A=(-97875) * d^2
    B=(14208750) * d^3
    return EllipticCurve([A,B])

def calC16_1(t,d):
    A=(-432) * d^2 * (t^8 + 240*t^6 + 2144*t^4 + 3840*t^2 + 256)
    B=(-3456) * d^3 * (t^4 + 24*t^2 + 16) * (t^4 - 24*t^3 + 24*t^2 - 96*t + 16) * (t^4 + 24*t^3 + 24*t^2 + 96*t + 16)
    return EllipticCurve([A,B])

def calC16_2(t,d):
    A=(-27) * d^2 * (t^8 + 240*t^7 + 2160*t^6 + 6720*t^5 + 17504*t^4 + 26880*t^3 + 34560*t^2 + 15360*t + 256)
    B=(-54) * d^3 * (t^4 + 24*t^3 + 24*t^2 + 96*t + 16) * (t^8 - 528*t^7 - 3984*t^6 - 14784*t^5 - 31648*t^4 - 59136*t^3 - 63744*t^2 - 33792*t + 256)
    return EllipticCurve([A,B])

def calC16_3(t,d):
    A=(-432) * d^2 * (t^8 - 240*t^7 + 2160*t^6 - 6720*t^5 + 17504*t^4 - 26880*t^3 + 34560*t^2 - 15360*t + 256)
    B=(-3456) * d^3 * (t^4 - 24*t^3 + 24*t^2 - 96*t + 16) * (t^8 + 528*t^7 - 3984*t^6 + 14784*t^5 - 31648*t^4 + 59136*t^3 - 63744*t^2 + 33792*t + 256)
    return EllipticCurve([A,B])

def calC16_4(t,d):
    A=(-6912) * d^2 * (t^4 - 4*t^3 + 8*t^2 + 16*t + 16) * (t^4 + 4*t^3 + 8*t^2 - 16*t + 16)
    B=(-221184) * d^3 * (t^2 - 4*t - 4) * (t^2 + 4*t - 4) * (t^4 + 16) * (t^4 + 24*t^2 + 16)
    return EllipticCurve([A,B])

def calC16_5(t,d):
    A=(-6912) * d^2 * (t^4 - 16*t^3 + 8*t^2 + 64*t + 16) * (t^4 + 16*t^3 + 8*t^2 - 64*t + 16)
    B=(-221184) * d^3 * (t^2 - 4*t - 4) * (t^2 + 4*t - 4) * (t^8 + 528*t^6 - 4000*t^4 + 8448*t^2 + 256)
    return EllipticCurve([A,B])

def calC16_6(t,d):
    A=(-110592) * d^2 * (t^8 - 16*t^4 + 256)
    B=(-14155776) * d^3 * (t^4 - 32) * (t^4 - 8) * (t^4 + 16)
    return EllipticCurve([A,B])

def calC16_7(t,d):
    A=(-110592) * d^2 * (t^8 - 256*t^4 + 4096)
    B=(-14155776) * d^3 * (t^4 - 32) * (t^8 + 512*t^4 - 8192)
    return EllipticCurve([A,B])

def calC16_8(t,d):
    A=(-1769472) * d^2 * (t^8 - 16*t^4 + 16)
    B=(-905969664) * d^3 * (t^4 - 8) * (t^8 - 16*t^4 - 8)
    return EllipticCurve([A,B])

def calC17_1(d):
    A=(-247394115) * d^2
    B=(-1679010134850) * d^3
    return EllipticCurve([A,B])

def calC17_2(d):
    A=(-3940515) * d^2
    B=(3010787550) * d^3
    return EllipticCurve([A,B])

def calC18_1(t,d):
    A=(-3) * d^2 * (t^3 + 6*t^2 + 4) * (t^9 + 234*t^8 + 756*t^7 + 2172*t^6 + 1872*t^5 + 3024*t^4 + 48*t^3 + 3744*t^2 + 64)
    B=(-2) * d^3 * (t^6 + 24*t^5 + 24*t^4 + 92*t^3 - 48*t^2 + 96*t - 8) * (t^12 - 528*t^11 - 3984*t^10 - 14792*t^9 - 27936*t^8 - 42624*t^7 - 37632*t^6 - 52992*t^5 - 25344*t^4 - 43520*t^3 - 6144*t^2 - 6144*t - 512)
    return EllipticCurve([A,B])

def calC18_2(t,d):
    A=(-48) * d^2 * (t^3 + 6*t - 2) * (t^9 + 234*t^7 - 6*t^6 + 756*t^5 - 936*t^4 + 2172*t^3 - 1512*t^2 + 936*t - 8)
    B=(-128) * d^3 * (t^6 + 24*t^5 + 24*t^4 + 92*t^3 - 48*t^2 + 96*t - 8) * (t^12 - 24*t^11 + 48*t^10 - 680*t^9 + 792*t^8 - 3312*t^7 + 4704*t^6 - 10656*t^5 + 13968*t^4 - 14792*t^3 + 7968*t^2 - 2112*t - 8)
    return EllipticCurve([A,B])

def calC18_3(t,d):
    A=(-243) * d^2 * (t^3 + 4) * (t^3 + 6*t^2 + 4) * (t^6 - 6*t^5 + 36*t^4 + 8*t^3 - 24*t^2 + 16)
    B=(-1458) * d^3 * (t^2 + 2*t - 2) * (t^4 - 8*t^3 - 8*t - 8) * (t^4 - 2*t^3 + 6*t^2 + 4*t + 4) * (t^8 + 8*t^7 + 64*t^6 - 16*t^5 - 56*t^4 + 128*t^3 + 64*t^2 - 64*t + 64)
    return EllipticCurve([A,B])

def calC18_4(t,d):
    A=(-3888) * d^2 * (t^3 - 2) * (t^3 + 6*t - 2) * (t^6 - 6*t^4 - 4*t^3 + 36*t^2 + 12*t + 4)
    B=(-93312) * d^3 * (t^2 + 2*t - 2) * (t^4 - 2*t^3 - 8*t - 2) * (t^4 - 2*t^3 + 6*t^2 + 4*t + 4) * (t^8 + 2*t^7 + 4*t^6 - 16*t^5 - 14*t^4 + 8*t^3 + 64*t^2 - 16*t + 4)
    return EllipticCurve([A,B])

def calC18_5(t,d):
    A=(-19683) * d^2 * (t^3 + 4) * (t^9 - 12*t^6 + 48*t^3 + 64)
    B=(-1062882) * d^3 * (t^6 - 4*t^3 - 8) * (t^12 - 8*t^9 - 512*t^3 - 512)
    return EllipticCurve([A,B])

def calC18_6(t,d):
    A=(-314928) * d^2 * (t^3 - 2) * (t^9 - 6*t^6 - 12*t^3 - 8)
    B=(-68024448) * d^3 * (t^6 - 4*t^3 - 8) * (t^12 - 8*t^9 - 8*t^3 - 8)
    return EllipticCurve([A,B])

def calC19_1(d):
    A=(-219488) * d^2
    B=(-39617584) * d^3
    return EllipticCurve([A,B])

def calC19_2(d):
    A=(-608) * d^2
    B=(5776) * d^3
    return EllipticCurve([A,B])

def calC21_1(d):
    A=(-1396035) * d^2
    B=(634881726) * d^3
    return EllipticCurve([A,B])

def calC21_2(d):
    A=(-1104435) * d^2
    B=(907504398) * d^3
    return EllipticCurve([A,B])

def calC21_3(d):
    A=(3645) * d^2
    B=(-13122) * d^3
    return EllipticCurve([A,B])

def calC21_4(d):
    A=(-54675) * d^2
    B=(-5156946) * d^3
    return EllipticCurve([A,B])

def calC25_1(t,d):
    A=(-27) * d^2 * (t^2 + 4) * (t^10 + 240*t^9 + 2170*t^8 + 8880*t^7 + 34835*t^6 + 83748*t^5 + 206210*t^4 + 313380*t^3 + 503545*t^2 + 424740*t + 375376)
    B=(-54) * d^3 * (t^2 + 4)^2 * (t^4 + 6*t^3 + 21*t^2 + 36*t + 61) * (t^10 - 510*t^9 - 13580*t^8 - 36870*t^7 - 190915*t^6 - 393252*t^5 - 1068040*t^4 - 1508370*t^3 - 2581955*t^2 - 2087010*t - 1885124)
    return EllipticCurve([A,B])

def calC25_2(t,d):
    A=(-16875) * d^2 * (t^2 + 4) * (t^2 + 3*t + 1) * (t^4 - 4*t^3 + 11*t^2 - 14*t + 31) * (t^4 + t^3 + 11*t^2 - 4*t + 16)
    B=(-843750) * d^3 * (t^2 - 2*t - 4) * (t^2 + 4)^2 * (t^4 + 3*t^2 + 1) * (t^4 - 4*t^3 + 21*t^2 - 34*t + 41) * (t^4 + 6*t^3 + 21*t^2 + 36*t + 61)
    return EllipticCurve([A,B])

def calC25_3(t,d):
    A=(-10546875) * d^2 * (t^2 + 4) * (t^10 + 10*t^8 + 35*t^6 - 12*t^5 + 50*t^4 - 60*t^3 + 25*t^2 - 60*t + 16)
    B=(-13183593750) * d^3 * (t^2 + 4)^2 * (t^4 + 3*t^2 + 1) * (t^10 + 10*t^8 + 35*t^6 - 18*t^5 + 50*t^4 - 90*t^3 + 25*t^2 - 90*t + 76)
    return EllipticCurve([A,B])

def calC27_1(d):
    A=(-4320) * d^2
    B=(-109296) * d^3
    return EllipticCurve([A,B])

def calC27_2(d):
    A=0
    B=- 432*d^3
    return EllipticCurve([A,B])

def calC27_3(d):
    A=0
    B=16*d^3
    return EllipticCurve([A,B])

def calC27_4(d):
    A=(-480) * d^2
    B=(4048) * d^3
    return EllipticCurve([A,B])

def calC37_1(d):
    A=(-269675595) * d^2
    B=(-1704553285050) * d^3
    return EllipticCurve([A,B])

def calC37_2(d):
    A=(-10395) * d^2
    B=(444150) * d^3
    return EllipticCurve([A,B])

def calC43_1(d):
    A=(-25442240) * d^2
    B=(-49394836848) * d^3
    return EllipticCurve([A,B])

def calC43_2(d):
    A=(-13760) * d^2
    B=(621264) * d^3
    return EllipticCurve([A,B])

def calC67_1(d):
    A=(-529342880) * d^2
    B=(-4687634371504) * d^3
    return EllipticCurve([A,B])

def calC67_2(d):
    A=(-117920) * d^2
    B=(15585808) * d^3
    return EllipticCurve([A,B])

def calC163_1(d):
    A=(-924354639680) * d^2
    B=(-342062961763303088) * d^3
    return EllipticCurve([A,B])

def calC163_2(d):
    A=(-34790720) * d^2
    B=(78984748304) * d^3
    return EllipticCurve([A,B])



def isog_curves(n, t, d):
    """
    Returns a list of n-isogenous elliptic curves.

    Given isogeny degree n, returns calCn_i(t, d) for all curves $C_{n,i}(t, d)$ in the isogeny class.

    INPUT:

    - ``n`` -- integer in IsogDegrees list
    - ``t`` -- algebraic number
    - ``d`` -- algebraic number

    OUTPUT: a list of n-isogenous elliptic curves parameterized by t and d.

    EXAMPLES:

        sage: E1, E2 = isog_curves(2, 1, 1)
        sage: print(E1.is_isogenous(E2))
        True
        sage: print(E1.isogeny_degree(E2))
        2
    """
    IsogDegrees = [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 25, 27, 37, 43, 67, 163]
    if n not in IsogDegrees:
        return([])
    elif n == 2:
        E1 = calC2_1(t, d)
        E2 = calC2_2(t, d)
        return([E1, E2])
    elif n == 3:
        E1 = calC3_1(t, d)
        E2 = calC3_2(t, d)
        return([E1, E2])
    elif n == 4:
        E1 = calC4_1(t, d)
        E2 = calC4_2(t, d)
        E3 = calC4_3(t, d)
        E4 = calC4_4(t, d)
        return([E1, E2, E3, E4])
    elif n == 5:
        E1 = calC5_1(t, d)
        E2 = calC5_2(t, d)
        return([E1, E2])
    elif n == 6:
        E1 = calC6_1(t, d)
        E2 = calC6_2(t, d)
        E3 = calC6_3(t, d)
        E4 = calC6_4(t, d)
        return([E1, E2, E3, E4])
    elif n == 7:
        E1 = calC7_1(t, d)
        E2 = calC7_2(t, d)
        return([E1, E2])
    elif n == 8:
        E1 = calC8_1(t, d)
        E2 = calC8_2(t, d)
        E3 = calC8_3(t, d)
        E4 = calC8_4(t, d)
        E5 = calC8_5(t, d)
        E6 = calC8_6(t, d)
        return([E1, E2, E3, E4, E5, E6])
    elif n == 9:
        E1 = calC9_1(t, d)
        E2 = calC9_2(t, d)
        E3 = calC9_3(t, d)
        return([E1, E2, E3])
    elif n == 10:
        E1 = calC10_1(t, d)
        E2 = calC10_2(t, d)
        E3 = calC10_3(t, d)
        E4 = calC10_4(t, d)
        return([E1, E2, E3, E4])
    elif n == 11:
        E1 = calC11_1(d)
        E2 = calC11_2(d)
        E3 = calC11_3(d)
        E4 = calC11_4(d)
        return([E1, E2, E3, E4])
    elif n == 12:
        E1 = calC12_1(t, d)
        E2 = calC12_2(t, d)
        E3 = calC12_3(t, d)
        E4 = calC12_4(t, d)
        E5 = calC12_5(t, d)
        E6 = calC12_6(t, d)
        E7 = calC12_7(t, d)
        E8 = calC12_8(t, d)
        return([E1, E2, E3, E4, E5, E6, E7, E8])
    elif n == 13:
        E1 = calC13_1(t, d)
        E2 = calC13_2(t, d)
        return([E1, E2])
    elif n == 14:
        E1 = calC14_1(d)
        E2 = calC14_2(d)
        E3 = calC14_3(d)
        E4 = calC14_4(d)
        return([E1, E2, E3, E4])
    elif n == 15:
        E1 = calC15_1(d)
        E2 = calC15_2(d)
        E3 = calC15_3(d)
        E4 = calC15_4(d)
        return([E1, E2, E3, E4])
    elif n == 16:
        E1 = calC16_1(t, d)
        E2 = calC16_2(t, d)
        E3 = calC16_3(t, d)
        E4 = calC16_4(t, d)
        E5 = calC16_5(t, d)
        E6 = calC16_6(t, d)
        E7 = calC16_7(t, d)
        E8 = calC16_8(t, d)
        return([E1, E2, E3, E4, E5, E6, E7, E8])
    elif n == 17:
        E1 = calC17_1(d)
        E2 = calC17_2(d)
        return([E1, E2])
    elif n == 18:
        E1 = calC18_1(t, d)
        E2 = calC18_2(t, d)
        E3 = calC18_3(t, d)
        E4 = calC18_4(t, d)
        E5 = calC18_5(t, d)
        E6 = calC18_6(t, d)
        return([E1, E2, E3, E4, E5, E6])
    elif n == 19:
        E1 = calC19_1(d)
        E2 = calC19_2(d)
        return([E1, E2])
    elif n == 21:
        E1 = calC21_1(d)
        E2 = calC21_2(d)
        E3 = calC21_3(d)
        E4 = calC21_4(d)
        return([E1, E2, E3, E4])
    elif n == 25:
        E1 = calC25_1(t, d)
        E2 = calC25_2(t, d)
        E3 = calC25_3(t, d)
        return([E1, E2, E3])
    elif n == 27:
        E1 = calC27_1(d)
        E2 = calC27_2(d)
        E3 = calC27_3(d)
        E4 = calC27_4(d)
        return([E1, E2, E3, E4])
    elif n == 37:
        E1 = calC37_1(d)
        E2 = calC37_2(d)
        return([E1, E2])
    elif n == 43:
        E1 = calC43_1(d)
        E2 = calC43_2(d)
        return([E1, E2])
    elif n == 67:
        E1 = calC67_1(d)
        E2 = calC67_2(d)
        return([E1, E2])
    elif n == 163:
        E1 = calC163_1(d)
        E2 = calC163_2(d)
        return([E1, E2])
    else:
        raise NotImplementedError