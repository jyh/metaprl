# Format of the lines:
#     name / operator term / number of args / res type / arg1 type / arg2 type


#--------------------------------------------------------------------------
# Unary operators.
#--------------------------------------------------------------------------


# Unary operators - tyEnum.

notEnumOp / notEnumOp[i:n] / 1 / tyEnum[i:n] / tyEnum[i:n]


# Unary operators - tyInt.

uminusIntOp / uminusIntOp / 1 / tyInt / tyInt
notIntOp / notIntOp / 1 / tyInt / tyInt
absIntOp / absIntOp / 1 / tyInt / tyInt


# Unary operators - tyRawInt.
uminusRawIntOp / uminusRawIntOp[p:n, s:s] / 1 / tyRawInt[p:n, s:s] / tyRawInt[p:n, s:s]
notRawIntOp / notRawIntOp[p:n, s:s] / 1 / tyRawInt[p:n, s:s] / tyRawInt[p:n, s:s]

# XXX: rawBitFieldOp should go here.


# Unary operators - tyFloat.

uminusFloatOp / uminusFloatOp[p:n] / 1 / tyFloat[p:n] / tyFloat[p:n]
absFloatOp / absFloatOp[p:n] / 1 / tyFloat[p:n] / tyFloat[p:n]
sinFloatOp / sinFloatOp[p:n] / 1 / tyFloat[p:n] / tyFloat[p:n]
cosFloatOp / cosFloatOp[p:n] / 1 / tyFloat[p:n] / tyFloat[p:n]
tanFloatop / tanFloatOp[p:n] / 1 / tyFloat[p:n] / tyFloat[p:n]
asinFloatOp / asinFloatOp[p:n] / 1 / tyFloat[p:n] / tyFloat[p:n]
atanFloatOp / atanFloatOp[p:n] / 1 / tyFloat[p:n] / tyFloat[p:n]
sinhFloatOp / sinhFloatOp[p:n] / 1 / tyFloat[p:n] / tyFloat[p:n]
coshFloatOp / coshFloatOp[p:n] / 1 / tyFloat[p:n] / tyFloat[p:n]
tanhFloatOp / tanhFloatOp[p:n] / 1 / tyFloat[p:n] / tyFloat[p:n]
expFloatOp / expFloatOp[p:n] / 1 / tyFloat[p:n] / tyFloat[p:n]
logFloatOp / logFloatOp[p:n] / 1 / tyFloat[p:n] / tyFloat[p:n]
sqrtFloatOp / sqrtFloatOp[p:n] / 1 / tyFloat[p:n] / tyFloat[p:n]
ceilFloatOp / ceilFloatOp[p:n] / 1 / tyFloat[p:n] / tyFloat[p:n]
floorFloatOp / floorFloatOp[p:n] / 1 / tyFloat[p:n] / tyFloat[p:n]


# Unary operators - coercions.

intOfFloatOp / intOfFloatOp[p:n] / 1 / tyInt / tyFloat[p:n]
intOfRawIntOp / intOfRawIntOp[p:n, s:s] / 1 / tyInt / tyRawInt[p:n, s:s]

floatOfIntOp / floatOfIntOp[p:n] / 1 / tyFloat[p:n] / tyInt
floatOfFloatOp / floatOfFloatOp[p1:n, p2:n] / 1 / tyFloat[p1:n] / tyFloat[p2:n]
floatOfRawIntOp / floatOfRawIntOp[fp:n, rp:n, s:s] / 1 / tyFloat[fp:n] / tyRawInt[rp:n, s:s]

rawIntOfIntOp / rawIntOfIntOp[p:n, s:s] / 1 / tyRawInt[p:n, s:s] / tyInt
rawIntOfEnumOp / rawIntOfEnumOp[p:n, s:s, i:n] / 1 / tyRawInt[p:n, s:s] / tyEnum[i:n]
rawIntOfFloatOp / rawIntOfFloatOp[rp:n, s:s, fp:n] / 1 / tyRawInt[rp:n, s:s] / tyFloat[fp:n]
rawIntOfRawIntOp / rawIntOfRawIntOp[dp:n, ds:s, sp:n, ss:s] / 1 / tyRawInt[dp:n, ds:s] / tyRawInt[sp:n, ss:s]

# XXX: rawIntOfPointerOp, pointerOfRawIntOp --- we don't understand these.

dtupleOfDTupleOp / dtupleOfDTupleOp{ 'tv; 'mtyl } / 1 / tyDTuple{ 'tv; none } / tyDTuple{ 'tv; some{ 'mtyl } }
unionOfUnionOp / unionOfUnionOp{ 'tv; 'tyl; 's1; 's2 } / 1 / tyUnion{ 'tv; 'tyl; 's1 } / tyUnion{ 'tv; 'tyl; 's2 }
rawDataOfFrameOp / rawDataOfFrameOp{ 'tv; 'tyl } / 1 / tyRawData / tyFrame{ 'tv; 'tyl }


#--------------------------------------------------------------------------
# Binary operators.
#--------------------------------------------------------------------------


# Binary operators - tyEnum.

andEnumOp / andEnumOp[i:n] / 2 / tyEnum[i:n] / tyEnum[i:n] / tyEnum[i:n]
orEnumOp / orEnumOp[i:n] / 2 / tyEnum[i:n] / tyEnum[i:n] / tyEnum[i:n]
xorEnumOp / xorEnumOp[i:n] / 2 / tyEnum[i:n] / tyEnum[i:n] / tyEnum[i:n]


# Binary operators - tyInt.

plusIntOp / plusIntOp / 2 / tyInt / tyInt / tyInt
minusIntOp / minusIntOp / 2 / tyInt / tyInt / tyInt
mulIntOp / mulIntOp / 2 / tyInt / tyInt / tyInt
divIntOp / divIntOp / 2 / tyInt / tyInt / tyInt
remIntOp / remIntOp / 2 / tyInt / tyInt / tyInt
lslIntOp / lslIntOp / 2 / tyInt / tyInt / tyInt
lsrIntOp / lsrIntOp / 2 / tyInt / tyInt / tyInt
asrIntOp / asrIntOp / 2 / tyInt / tyInt / tyInt
andIntOp / andIntOp / 2 / tyInt / tyInt / tyInt
orIntOp / orIntOp / 2 / tyInt / tyInt / tyInt
xorIntOp / xorIntOp / 2 / tyInt / tyInt / tyInt
maxIntOp / maxIntOp / 2 / tyInt / tyInt / tyInt

eqIntOp / eqIntOp / 2 / tyEnum[2] / tyInt / tyInt
neqIntOp / neqIntOp / 2 / tyEnum[2] / tyInt / tyInt
ltIntOp / ltIntOp / 2 / tyEnum[2] / tyInt / tyInt
leIntOp / leIntOp / 2 / tyEnum[2] / tyInt / tyInt
gtIntOp / gtIntOp / 2 / tyEnum[2] / tyInt / tyInt
geIntOp / geIntOp / 2 / tyEnum[2] / tyInt / tyInt
cmpIntOp / cmpIntOp / 2 / tyInt / tyInt / tyInt


# Binary operators - tyRawInt

plusRawIntOp / plusRawIntOp[p:n, s:s] / 2 / tyRawInt[p:n, s:s] / tyRawInt[p:n, s:s] / tyRawInt[p:n, s:s]
minusRawIntOp / minusRawIntOp[p:n, s:s] / 2 / tyRawInt[p:n, s:s] / tyRawInt[p:n, s:s] / tyRawInt[p:n, s:s]
mulRawIntOp / mulRawIntOp[p:n, s:s] / 2 / tyRawInt[p:n, s:s] / tyRawInt[p:n, s:s] / tyRawInt[p:n, s:s]
divRawIntOp / divRawIntOp[p:n, s:s] / 2 / tyRawInt[p:n, s:s] / tyRawInt[p:n, s:s] / tyRawInt[p:n, s:s]
remRawIntOp / remRawIntOp[p:n, s:s] / 2 / tyRawInt[p:n, s:s] / tyRawInt[p:n, s:s] / tyRawInt[p:n, s:s]
slRawIntOp / slRawIntOp[p:n, s:s] / 2 / tyRawInt[p:n, s:s] / tyRawInt[p:n, s:s] / tyRawInt[p:n, s:s]
srRawIntOp / srRawIntOp[p:n, s:s] / 2 / tyRawInt[p:n, s:s] / tyRawInt[p:n, s:s] / tyRawInt[p:n, s:s]
andRawIntOp / andRawIntOp[p:n, s:s] / 2 / tyRawInt[p:n, s:s] / tyRawInt[p:n, s:s] / tyRawInt[p:n, s:s]
orRawIntOp / orRawIntOp[p:n, s:s] / 2 / tyRawInt[p:n, s:s] / tyRawInt[p:n, s:s] / tyRawInt[p:n, s:s]
xorRawIntOp / xorRawIntOp[p:n, s:s] / 2 / tyRawInt[p:n, s:s] / tyRawInt[p:n, s:s] / tyRawInt[p:n, s:s]
maxRawIntOp / maxRawIntOp[p:n, s:s] / 2 / tyRawInt[p:n, s:s] / tyRawInt[p:n, s:s] / tyRawInt[p:n, s:s]
minRawIntOp / minRawIntOp[p:n, s:s] / 2 / tyRawInt[p:n, s:s] / tyRawInt[p:n, s:s] / tyRawInt[p:n, s:s]

# XXX: rawSetBitfieldOp should go here

eqRawIntOp / eqRawIntOp[p:n, s:s] / 2 / tyEnum[2] / tyRawInt[p:n, s:s] / tyRawInt[p:n, s:s]
neqRawIntOp / neqRawIntOp[p:n, s:s] / 2 / tyEnum[2] / tyRawInt[p:n, s:s] / tyRawInt[p:n, s:s]
ltRawIntOp / ltRawIntOp[p:n, s:s] / 2 / tyEnum[2] / tyRawInt[p:n, s:s] / tyRawInt[p:n, s:s]
leRawIntOp / leRawIntOp[p:n, s:s] / 2 / tyEnum[2] / tyRawInt[p:n, s:s] / tyRawInt[p:n, s:s]
gtRawIntOp / gtRawIntOp[p:n, s:s] / 2 / tyEnum[2] / tyRawInt[p:n, s:s] / tyRawInt[p:n, s:s]
geRawIntO / geRawIntOp[p:n, s:s] / 2 / tyEnum[2] / tyRawInt[p:n, s:s] / tyRawInt[p:n, s:s]
cmpRawIntOp / cmpRawIntOp[p:n, s:s] / 2 / tyInt / tyRawInt[p:n, s:s] / tyRawInt[p:n, s:s]


# Binary operators - tyFloat.

plusFloatOp / plusFloatOp[p:n] / 2 / tyFloat[p:n] / tyFloat[p:n] / tyFloat[p:n]
minusFloatOp / minusFloatOp[p:n] / 2 / tyFloat[p:n] / tyFloat[p:n] / tyFloat[p:n]
mulFloatOp / mulFloatOp[p:n] / 2 / tyFloat[p:n] / tyFloat[p:n] / tyFloat[p:n]
divFloatOp / divFloatOp[p:n] / 2 / tyFloat[p:n] / tyFloat[p:n] / tyFloat[p:n]
remFloatOp / remFloatOp[p:n] / 2 / tyFloat[p:n] / tyFloat[p:n] / tyFloat[p:n]
maxFloatOp / maxFloatOp[p:n] / 2 / tyFloat[p:n] / tyFloat[p:n] / tyFloat[p:n]
minFloatOp / minFloatOp[p:n] / 2 / tyFloat[p:n] / tyFloat[p:n] / tyFloat[p:n]

eqFloatOp / eqFloatOp[p:n] / 2 / tyEnum[2] / tyFloat[p:n] / tyFloat[p:n]
neqFloatOp / neqFloatOp[p:n] / 2 / tyEnum[2] / tyFloat[p:n] / tyFloat[p:n]
ltFloatOp / ltFloatOp[p:n] / 2 / tyEnum[2] / tyFloat[p:n] / tyFloat[p:n]
leFloatOp / leFloatOp[p:n] / 2 / tyEnum[2] / tyFloat[p:n] / tyFloat[p:n]
gtFloatOp / gtFloatOp[p:n] / 2 / tyEnum[2] / tyFloat[p:n] / tyFloat[p:n]
geFloatOp / geFloatOp[p:n] / 2 / tyEnum[2] / tyFloat[p:n] / tyFloat[p:n]
cmpFloatOp / cmpFloatOp[p:n] / 2 / tyInt / tyFloat[p:n] / tyFloat[p:n]

atan2FloatOp / atan2FloatOp[p:n] / 2 / tyFloat[p:n] / tyFloat[p:n] / tyFloat[p:n]
powerFloatOp / powerFloatOp[p:n] / 2 / tyFloat[p:n] / tyFloat[p:n] / tyFloat[p:n]
ldExpFloatIntOp / ldExpFloatIntOp[p:n] / 2 / tyFloat[p:n] / tyFloat[p:n] / tyInt


# Binary operators - pointers.

eqEqOp / eqEqOp{ 'ty } / 2 / tyEnum[2] / 'ty / 'ty
neqEqOp / neqEqOp{ 'ty } / 2 / tyEnum[2] / 'ty / 'ty
