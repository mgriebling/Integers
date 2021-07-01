/**
Implements integer values of arbitrary magnitude.
Copyright © 2002, 2003, 2015 Michael van Acken and Michael Griebling

This module is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public License
as published by the Free Software Foundation; either version 2 of
the License, or (at your option) any later version.

This module is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License along with Integers. If not, write to the Free Software Foundation,
59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

This module is a reformulation of (parts of) Python's *longobject.c*
in Swift.  Optimizations like Karatsuba multiplication and string
conversion for power of two base have been omitted.  All errors are mine,
of course.

Added algorithms are from Knuth: "The Art Of Computer Programming",
Vol 2, section 4.3.1

Ported to Swift by Michael Griebling, 18 July 2015.
*/

import Foundation

// Definition of power operator
infix operator ** : ExponentPrecedence
precedencegroup ExponentPrecedence {
    associativity: left
    higherThan: MultiplicationPrecedence
}

public func ** (base: Int, power: Int) -> Integer { return Integer(base) ** power }

public struct Integer : Codable {
    
    /// Basic data type representing one *Digit* of the *Integer*.
    public typealias Digit = Int32
    fileprivate typealias TwoDigits = Int64
    
    /// Number of bits in a *Digit*.  Minimum is 6.
    fileprivate static let shift : Digit = 30
    /// Modulo base of a *Digit* = 2^shift
    fileprivate static let base : Digit = 1 << shift
    fileprivate static let mask : Digit = (1 << shift) - 1
    
    /** Stores an integer number of arbitrary size.  The absolute value of a
        number is equal to *∑ digit[i]\*2^(shift\*i)* for 0 ≤ *i* < *size* where
        *size* = `digit.count`.  Negative numbers are represented
        with *negative = true*, and zero by *size* = 0.  In a
        normalized number, *digit[size-1]* (the most significant digit) is never zero.
        For all valid *i*, *0 ≤ digit[i] ≤ mask*.  */
    
    fileprivate var digit: [Digit]
    fileprivate var negative: Bool
    
    static public let zero = Integer()
    static public let one = Integer(1)
    
    fileprivate static var powerOf2 : [Int] {
        var array = [Int](repeating: -1, count: 38)
        array[2] = 1; array[4] = 2; array[8] = 3
        array[16] = 4; array[32] = 5
        return array
    }
    
    public init (size : Int = 0, negative: Bool = false) {
        digit = [Digit](repeating: 0, count: size)
        self.negative = negative
    }
    
    init (_ str: String, withBase: Int) {
        self.init()
        self = Integer.fromString(str, inputBase: withBase)
    }
    
    init(_ int : Int) {
        self.init(exactly: int)
    }
    
    init (_ d: Double) {
        self.init(Int(d))
    }
    
    /// Creates an Integer from a string with base 10 as a default.
    /// Prefixes of "0x", "0b", "0o" allow hexadecimal, binary, and octal inputs, respectively.
    public init (_ str: String) {
        func hasPrefix (_ s: String) -> Bool { return str.hasPrefix("-"+s) || str.hasPrefix(s) }
        
        let s = str.trimmingCharacters(in: CharacterSet.whitespaces)
        if hasPrefix("0x") { self.init(s.replacingOccurrences(of: "0x", with: ""), withBase: 16) }
        else if hasPrefix("0o") { self.init(s.replacingOccurrences(of: "0o", with: ""), withBase: 8) }
        else if hasPrefix("0b") { self.init(s.replacingOccurrences(of: "0b", with: ""), withBase: 2) }
        else { self.init(s, withBase: 10) }
    }
    
    func isEqual (_ n: Integer) -> Bool { return digit == n.digit && negative == n.negative }
    
    fileprivate static func Normalize(_ a: inout Integer) {
        let size = a.digit.count
        var i = size
        while i != 0 && a.digit[i-1] == 0 { i -= 1 }
        
        // remove leading zeros
        if i != size { a.digit.removeSubrange(i..<size) }
    }
    
    /** Adds the absolute values of two integers.  */
    fileprivate static func AddAbs (_ a: Integer, b: Integer) -> Integer {
        let x, y : Integer
        
        // Ensure x > y
        if a.digit.count < b.digit.count {
            x = b; y = a
        } else {
            x = a; y = b
        }
        let sizeA = x.digit.count
        let sizeB = y.digit.count
        var z = Integer(size: sizeA+1)
        var carry : Digit = 0
        for i in 0..<sizeB {
            carry += x.digit[i] + y.digit[i]
            z.digit[i] = carry & mask
            carry >>= shift
        }
        for i in sizeB..<sizeA {
            carry += x.digit[i]
            z.digit[i] = carry & mask
            carry >>= shift
        }
        z.digit[sizeA] = carry
        Normalize(&z)
        return z
    }
    
    public var isZero : Bool     { return digit.count == 0 }
    public var isNegative : Bool { return negative }
    public var sign : Int        { return negative ? -1 : isZero ? 0 : 1 }
    
    public func abs() -> Integer { return negative ? -self : self }
    
    public var integer : Int {
        let limit = Int.max / Int(Integer.base)
        var count = digit.count-1
        var int = Int(digit.last ?? 0)
        while count > 0 && int < limit {
            int *= Int(Integer.base)
            int += Int(digit[count]); count -= 1
        }
        if count > 0 { return negative ? Int.min : Int.max }
        return negative ? -Int(int) : Int(int)
    }
    
    public var double : Double {
        let (x, e) = scaledDouble()
        if e > Int(Int32.max / Integer.shift) { return Double.infinity }
        return ldexp(x, Int32(e) * Integer.shift)
    }
    
    func scaledDouble() -> (x: Double, e: Int) {
        let nBitsWanted = 57    // maximum bits in Double
        var nBitsNeeded = nBitsWanted - 1
        var i = digit.count
        if i == 0 { return (x:0, e:0) }
        i -= 1
        var x = Double(digit[i])
        let multiplier = Double(Integer.base)
        while i > 0 && nBitsNeeded > 0 {
            i -= 1
            x = x * multiplier + Double(digit[i])
            nBitsNeeded -= Int(Integer.shift)
        }
        
        /* There are i digits we didn't shift in.  Pretending they're all
           zeros, the true value is x * 2 **(i*shift) */
        assert(x > 0, "x <= 0 in scaledDoubled()")
        return (x: negative ? -x : x, e: i)
    }
    
    func cmp (_ b: Integer) -> Int {
        let sizea = digit.count
        let sizeb = b.digit.count
        if sizea > sizeb {
            return negative ? -1 : 1
        } else if sizea < sizeb {
            return b.negative ? 1 : -1
        } else {
            var i = sizea
            repeat { i -= 1 } while i >= 0 && digit[i] == b.digit[i]
            if i < 0 {
                return 0
            } else if digit[i] > b.digit[i] {
                return negative ? -1 : 1
            } else {
                return b.negative ? 1 : -1
            }
        }
    }
    
    /** Subtract the absolute value of two integers.  */
    fileprivate static func SubAbs (_ a: Integer, b: Integer) -> Integer {
        var x = a
        var y = b
        var sign = false
        
        // Ensure x > y
        if a.digit.count < b.digit.count {
            x = b; y = a
            sign = true
        } else if a.digit.count == b.digit.count {
            /* find highest digit where a and b differ */
            var i = a.digit.count-1
            while i >= 0 && a.digit[i] == b.digit[i] { i -= 1 }
            if i < 0 {
                return zero
            } else if a.digit[i] < b.digit[i] {
                x = b; y = a
                sign = true
            }
        }
        
        let sizeA = x.digit.count
        let sizeB = y.digit.count
        var z = Integer(size: sizeA, negative: sign)
        var borrow: Digit = 0
        for i in 0..<sizeB {
            borrow = x.digit[i]-y.digit[i]-borrow
            z.digit[i] = borrow & mask
            borrow >>= shift
            borrow &= 1 /* keep only 1 sign bit */
        }
        for i in sizeB..<sizeA {
            borrow = x.digit[i]-borrow
            z.digit[i] = borrow & mask
            borrow >>= shift
            borrow &= 1
        }
        assert(borrow == 0, "SubAbs borrow != 0")
        Normalize(&z)
        return z
    }
    
    /// Grade school multiplication, ignoring the signs.
    /// - Returns: The absolute value of the product of *a* and *b*.
    fileprivate static func MulAbs (_ a: Integer, b: Integer) -> Integer {
        var carry: TwoDigits
        let sizeA = a.digit.count
        let sizeB = b.digit.count
        var z = Integer(size:sizeA+sizeB)
        
        for i in 0..<sizeA {
            let f = TwoDigits(a.digit[i])
            carry = 0
            for j in 0..<sizeB {
                carry += TwoDigits(z.digit[i+j]) + TwoDigits(b.digit[j]) * f
                assert(carry >= 0, "MulAbs carry < 0")
                z.digit[i+j] = Digit(carry & TwoDigits(mask))
                carry >>= TwoDigits(shift)
            }
            var j = sizeB
            while carry != 0 {
                carry += TwoDigits(z.digit[i+j])
                assert(carry >= 0, "MulAbs carry < 0")
                z.digit[i+j] = Digit(carry & TwoDigits(mask))
                carry >>= TwoDigits(shift)
                j += 1
            }
        }
        Normalize(&z)
        return z
    } // MulAbs;
    
    /// Add *self* to *b* and return the sum.
    /// - Note: Subtraction is performed by *self.add(b.negate())*.
    func add (_ b: Integer) -> Integer {
        if negative {
            if b.negative {
                var z = Integer.AddAbs(self, b:b)
                z.negative = true
                return z
            } else {
                return Integer.SubAbs(b, b:self)
            }
        } else {
            return b.negative ? Integer.SubAbs(self, b:b) : Integer.AddAbs(self, b:b)
        }
    }
    
    func mul (_ b: Integer) -> Integer {
        var z = Integer.MulAbs(self, b:b)
        if negative != b.negative { z.negative = !z.negative }
        return z
    }
    
    /** Divide *pin*, with *size* digits, by non-zero digit
    *n*, storing the quotient in *pout*, and returning the remainder.
    *pin[0]* and *pout[0]* point at the LSD.  It's OK for
    *pin=pout* on entry, which saves oodles of mallocs/frees in
    Integer format, but that should be done with great care since Integers are
    immutable.  */
    fileprivate static func InplaceDivRem1 (_ pout: inout [Digit], pin: [Digit], psize: Int, n: Digit) -> Digit {
        assert(n > 0 && n < base, "InplaceDivRem1 assertion failed")
        var rem: TwoDigits = 0
        for size in (0..<psize).reversed() {
            rem = (rem << TwoDigits(shift)) | TwoDigits(pin[size])
            let hi = rem / TwoDigits(n)
            pout[size] = Digit(hi)
            rem -= hi * TwoDigits(n)
        }
        return Digit(rem)
    } // InplaceDivRem1;
    
    /** Divide a long integer *a* by a digit *n*, returning both the quotient
    (as function result) and the remainder *rem*.
    The sign of *a* is ignored; *n* should not be zero. */
    fileprivate static func divRem (_ a: Integer, n: Digit, rem: inout Digit) -> Integer {
        assert(n > 0 && n < base, "DivRem1 assertion failed")
        let size = a.digit.count
        var z = Integer(size: size)
        rem = InplaceDivRem1(&z.digit, pin:a.digit, psize:size, n:n)
        Normalize(&z)
        return z
    }
    
    /** Multiply by a single digit *n* and add a single digit *add*, ignoring the sign. */
    fileprivate static func mulAdd (_ a: Integer, n: Digit, add: Digit) -> Integer {
        let sizeA = a.digit.count
        var z = Integer(size:sizeA+1)
        var carry = TwoDigits(add)
        for i in 0..<sizeA {
            carry += TwoDigits(a.digit[i]) * TwoDigits(n)
            z.digit[i] = Digit(carry & TwoDigits(mask))
            carry >>= TwoDigits(shift)
        }
        z.digit[sizeA] = Digit(carry)
        Normalize(&z)
        return z
    }
    
    /** Unsigned long division with remainder -- the algorithm.  */
    fileprivate static func divRemAbs (_ v1: Integer, w1: Integer, rem: inout Integer) -> Integer {
        let sizeW = w1.digit.count
        let d = Digit(TwoDigits(base) / TwoDigits(w1.digit[sizeW-1]+1))
        var v = mulAdd(v1, n:d, add:0)
        let w = mulAdd(w1, n:d, add:0)
        
        assert(v1.digit.count >= sizeW && sizeW > 1, "DivRemAbs assertion 1 failed")
        assert(sizeW == w.digit.count, "DivRemAbs assertion 2 failed")
        
        let sizeV = v.digit.count
        var a = Integer(size:sizeV-sizeW+1)
        var j = sizeV
        for k in (0..<a.digit.count).reversed() {
            let vj: TwoDigits = j >= sizeV ? 0 : TwoDigits(v.digit[j])
            let base = TwoDigits(Integer.base)
            let mask = TwoDigits(Integer.mask)
            let w1digit = TwoDigits(w.digit[sizeW-1])
            let w2digit = TwoDigits(w.digit[sizeW-2])
            let vdigit = TwoDigits(v.digit[j-1])
            var q = vj == w1digit ? mask : (vj*base + vdigit) / w1digit
            
            while w2digit*q > (vj*base + vdigit - q*w1digit)*base + TwoDigits(v.digit[j-2]) {
                q -= 1
            }
            
            var i = 0
            var carry: TwoDigits = 0
            while i < sizeW && i+k < sizeV {
                let z = TwoDigits(w.digit[i])*q
                let zz = TwoDigits(z / base)
                carry += TwoDigits(v.digit[i+k]) - z + zz*base
                v.digit[i+k] = Digit(carry & mask)
                carry >>= TwoDigits(shift)
                carry -= zz
                i += 1
            }
            
            if i+k < sizeV {
                carry += TwoDigits(v.digit[i+k])
                v.digit[i+k] = 0
            }
            
            if carry == 0 {
                a.digit[k] = Digit(q)
            } else {
                assert(carry == -1, "DivRemAbs carry != -1")
                a.digit[k] = Digit(q-1)
                carry = 0
                for i in 0..<sizeW where i+k < sizeV {
                    carry += TwoDigits(v.digit[i+k] + w.digit[i])
                    v.digit[i+k] = Digit(carry & mask)
                    carry >>= TwoDigits(shift)
                }
            }
            j -= 1
        }
        Normalize(&a)
        var dx : Digit = 0
        rem = divRem(v, n:d, rem:&dx)
        return a
    } // DivRemAbs;
    
    fileprivate static func DivRem (_ a: Integer, b: Integer) -> (div:Integer, mod: Integer) {
        var remDigit: Digit
        var rem, z: Integer
        
        let sizeA = a.digit.count
        let sizeB = b.digit.count
        
        assert(sizeB != 0, "Assert failed in DivRem")   /* division by zero? */
        if sizeA < sizeB || (sizeA == sizeB && a.digit[sizeA-1] < b.digit[sizeB-1]) {
            /* |a| < |b| */
            return (zero, a)
        } else {
            if sizeB == 1 {
                remDigit = 0
                z = divRem(a, n:b.digit[0], rem:&remDigit)
                rem = Integer(Int(remDigit))
            } else {
                rem = zero
                z = divRemAbs(a, w1:b, rem:&rem)
            }
            
            /* Set the signs.  The quotient z has the sign of a*b; the remainder r
            has the sign of a, so a = b*z + r.  */
            if a.negative != b.negative { z.negative = !z.negative }
            rem.negative = a.negative
            return (z, rem)
        }
    } // DivRem;
    
    func divMod (_ w: Integer) -> (div: Integer, mod: Integer) {
        let x = Integer.DivRem(self, b:w)
//        if (x.mod.isNegative && !w.isNegative) || (!x.mod.isNegative && w.isNegative) {
//            return (div: x.div - 1, mod: x.mod + w)
//        }
        return x
    } // DivMod;
    
    func div (_ w: Integer) -> Integer {
        let (div, _) = self.divMod(w)
        return div
    } // Div;
    
    func mod (_ w: Integer) -> Integer {
        let (_, mod) = self.divMod(w)
        return mod
    } // Mod;
    
    /** Convert an *Integer* object to a string, using a given conversion base.  */
    func description (_ outputBase: Int) -> String {
        let conversion : String = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ"
        var str = ""
        let sizeA = self.digit.count
        assert(outputBase >= 2 && outputBase <= 36, "Assert outputBase failed in description")
        
        if sizeA == 0 {
            return "0"
            
        } else if Integer.powerOf2[outputBase] > 0 {
            let baseBits = Integer.powerOf2[outputBase]
            let mask = TwoDigits(outputBase - 1)
            var accum: TwoDigits = 0
            var accumBits = 0
            
            for i in 0..<sizeA {
                accum += TwoDigits(digit[i]) << TwoDigits(accumBits)
                accumBits += Int(Integer.shift)
                assert(accumBits >= baseBits, "Assert in description")
                repeat {
                    let d = Int(accum & mask)
                    assert(d >= 0, "Assertion failed: Description d < 0")
                    let index = conversion.index(conversion.startIndex, offsetBy: d)   // advance(conversion.startIndex, d)
                    let c = conversion[index]
                    str = String(c) + str
                    accumBits -= baseBits
                    accum = accum >> TwoDigits(baseBits)
                } while !((accumBits < baseBits) && (i < sizeA-1) || (accum == 0))
            }
            
        } else {
            /* powbase <- largest power of outputBase that fits in a digit. */
            var powbase = outputBase  /* powbase == outputBase ** power */
            var power = 1
            while true {
                let temp = powbase * outputBase
                if temp > Int(Integer.base) { break }
                powbase = temp
                power += 1
            }
            
            /* Get a scratch area for repeated division. */
            var scratch = self
            var size = sizeA
            
            /* Repeatedly divide by powbase. */
            repeat {
                var ntostore = power
                var rem = Integer.InplaceDivRem1(&scratch.digit, pin:scratch.digit, psize:size, n:Digit(powbase))
                if scratch.digit[size-1] == 0 { size -= 1 }
                
                /* Break rem into digits. */
                assert(ntostore > 0, "Assertion in description ntostore")
                repeat {
                    let nextrem = rem / Digit(outputBase)
                    let d = rem - nextrem * Digit(outputBase)
                    assert(d >= 0, "Assertion failed: description d < 0")
                    let index = conversion.index(conversion.startIndex, offsetBy: Int(d))
                    let c = conversion[index]
                    str = String(c) + str
                    rem = nextrem
                    ntostore -= 1
                    /* Termination is a bit delicate:  must not
                    store leading zeroes, so must get out if
                    remaining quotient and rem are both 0. */
                } while !((ntostore == 0) || (size == 0 && rem == 0))
            } while size > 0
        }
        
        return negative ? "-" + str : str
    } // Format;
    
    
    static func fromString (_ str: String, inputBase: Int) -> Integer {
        var d: Int
        var negative = false
        
        assert((2 <= inputBase) && (inputBase <= 36), "toInteger assertion")
        
        /* uppercase and skip leading whitespace */
        var s = str.trimmingCharacters(in: CharacterSet.whitespacesAndNewlines)
        
        /* handle sign */
        if !s.isEmpty {
            if s.hasPrefix("-") {
                negative = true
                s.remove(at: s.startIndex)
            } else if s.hasPrefix("+") {
                s.remove(at: s.startIndex)
            }
        }
        
        var z = Integer.zero
        while !s.isEmpty {
            let c = s.remove(at: s.startIndex)
            d = strtol(String(c), nil, Int32(inputBase))
            z = Integer.mulAdd(z, n:Digit(inputBase), add:Digit(d))
        }
        z.negative = negative
        return z
    }
    
    /** Bitwise signed 1's complement.  The result equals -(a+1).  */
    func invert() -> Integer {
        var a = Integer.mulAdd(self, n: 1, add: 1)  // self.add(Integer.one)
        a.negative = !negative
        return a
    } // Invert;
    
    func lShift (_ n: Int) -> Integer {
        assert(n >= 0, "lShift assertion: shift is negative")
        let wordShift = n / Int(Integer.shift)
        let remShift = TwoDigits(Digit(n) % Integer.shift)
        
        let oldSize = digit.count
        var newSize = oldSize+wordShift
        if remShift != 0 { newSize += 1 }
        
        var z = Integer(size: newSize)
        z.negative = negative
        var accum: TwoDigits = 0
        var i = wordShift
        for j in 0..<oldSize {
            accum |= TwoDigits(digit[j]) << remShift
            z.digit[i] = Digit(accum & TwoDigits(Integer.mask))
            accum >>= TwoDigits(Integer.shift)
            i += 1
        }
        if remShift != 0 {
            z.digit[newSize-1] = Digit(accum)
        } else {
            assert(accum == 0, "lShift assertion: remShift == 0")
        }
        Integer.Normalize(&z)
        return z
    } // LShift;
    
    func rShift (_ n: Int) -> Integer {
        assert(n >= 0, "rShift assertion: shift is negative")
        if negative {
            let a = self.invert().rShift(n)
            return a.invert()
        } else {
            let wordShift = n / Int(Integer.shift)
            let newSize = digit.count - wordShift
            if newSize <= 0 {
                return Integer.zero
            } else {
                let loShift = Digit(n) % Integer.shift
                let hiShift = Integer.shift - loShift
                let loMask = Int32(1 << hiShift) - 1
                let hiMask = Int32(Integer.mask) ^ loMask
                var z = Integer(size: newSize)
                var j = wordShift
                for i in 0..<newSize {
                    z.digit[i] = (digit[j] >> loShift) & loMask
                    if i+1 < newSize {
                        z.digit[i] |= (digit[j+1] << hiShift) & hiMask
                    }
                    j += 1
                }
                Integer.Normalize(&z)
                return z
            }
        }
    } // RShift;
    
    /// Euclid's gcd algorithm  (very elegant and very ancient!)
    ///  - Returns: Greatest common divisor of *m* and *n* where *m* = *self*
    ///  - Precondition: m ≥ n, n > 0
    func gcd (_ n: Integer) -> Integer {
        var x = self.abs()
        var y = n.abs()
        
        /* To start everything must be non-negative and x >= y */
        if x < y { let swap=x; x=y; y=swap }  // swap x and y so that x >= y
        
        while !y.isZero {
            let swap=x.mod(y)    /* division algorithm */
            x=y; y=swap            /* set up next iteration */
        }
        return x
    }
    
    /// - Returns: x^exp where x = *self*.
    /// - Precondition: x ≥ 0
    func power (_ exp: Int) -> Integer {
        var x = self
        var lexp = exp
        if exp<0 { return Integer.zero }  /* x**-exp = 0 */
        var y = Integer.one
        while lexp > 0 {
            if lexp & 1 == 1 { y=y.mul(x) }
            lexp >>= 1
            if lexp > 0 { x=x.mul(x) }
        }
        return y
    }
    
    /// - Returns: x! = x(x-1)(x-2)...(2)(1) where *x* = *self*.
    /// - Precondition: *x* ≥ 0
    func factorial () -> Integer {
        let x = self.integer
        if x < 0 { return Integer.zero }    /* out of range */
        if x < 2 { return Integer.one }        /* 0! & 1! */
        
        var f = Integer.one
        for lx in 2...Digit(x) {
            f = Integer.mulAdd(f, n: lx, add: 0)  /* f=f*x */
        }
        return f
    }
    
    /** - Returns: *digits*-length random number.
    Note: Actual number of digits ≥ *digits*.
    Default length for digits ≦ 0 is 50. */
    static func random (_ digits: Int = 0) -> Integer {
        let B = mask
        let defaultDigits = 50
        let udigits = Double(digits <= 0 ? defaultDigits : digits)
        let ndigits = 3.321928095 / Double(shift)  // number of Digits per base 10 digit
        var n = Integer(size: max(1,Int(round(udigits*ndigits))))  /* n size = digits*log(10)/log(base) */
        n.digit[0] = Digit(Foundation.arc4random() & UInt32(B))
        for i in 1..<n.digit.count { n.digit[i] = Digit(Foundation.arc4random() & UInt32(B)) }
        return n
    }
    
    /* ******************************************************* */
    /*  Logical operations                                     */
    
    /** - Returns: Extension of the receiver to *max* digits */
    fileprivate func extendedTo (_ size: Int) -> Integer {
        if digit.count == size { return self }
        var y = Integer(size: size)
        y.negative = negative
        for i in 0..<digit.count { y.digit[i] = digit[i] }
        return y
    }
    
    /** Creates a limited *size* unsigned version of *self* */
    fileprivate func unsigned (_ size: Int) -> Integer {
        if !negative { return self.extendedTo(size) }
        var a = Integer(size: size)
        
        /* convert to 1's complement */
        let b = (self+1).extendedTo(size)
        for i in 0..<size { a.digit[i] = ~b.digit[i] & Integer.mask }
        return a
    }
    
    /** Creates a normalized signed version of *z* */
    fileprivate static func signed (_ z: inout Integer) {
        let size = z.digit.count
        let signMask = Digit(1 << (shift-1))   // sign bit mask
        if size == 0 { return }
        z.negative = z.digit[size-1] & signMask != 0
        
        // convert back to two's complement format
        if z.negative {
            for i in 0..<size { z.digit[i] = ~z.digit[i] & Integer.mask }
            z--
        }
        Normalize(&z)
    }
    
    /** - Returns: *op()* applied to *self* and *y*. */
    fileprivate func lop (_ y: Integer, op: (Digit, Digit) -> Digit) -> Integer {
        let size = max(digit.count, y.digit.count)
        let a = self.unsigned(size)
        let b = y.unsigned(size)
        var z = Integer(size: size)
        for i in 0..<size { z.digit[i] = op(a.digit[i], b.digit[i]) }
        Integer.signed(&z)
        return z
    }
    
    /** - Returns: Bitwise **and** of *self* and *y* */
    func and (_ y : Integer) -> Integer { return self.lop(y, op: &) }
    
    /** - Returns: Bitwise **or** of *self* and *y* */
    func or (_ y : Integer) -> Integer { return self.lop(y, op: |) }
    
    /** - Returns: Bitwise **xor** of *self* and *y* */
    func xor (_ y : Integer) -> Integer { return self.lop(y, op: ^) }
    
    /** - Returns: *self* with *bit* set in the receiver. */
    func setBit(_ bit: Int) -> Integer { return self | (1 << bit) }
    
    /** - Returns: *self* with *bit* cleared in the receiver. */
    func clearBit(_ bit: Int) -> Integer { return self & ~(1 << bit) }
    
    /** - Returns: *self* with *bit* toggled in the receiver. */
    func toggleBit(_ bit: Int) -> Integer { return self ^ (1 << bit) }
    
    static public func ** (base: Integer, power: Int) -> Integer { return base.power(power) }
    
} // Integer

extension Integer : CustomStringConvertible {
    
    /*  CustomStringConvertible compliance */
    public var description: String { return self.description(10) }
    
}

extension Integer : CustomDebugStringConvertible {
    
    public var debugDescription: String {
        var s = "size=\(digit.count), digits="
        for i in 0..<digit.count {
            s += "\(digit[i]) "
        }
        s += ", base=\(Integer.base)"
        return s
    }
    
}

extension Integer : ExpressibleByStringLiteral {
    
    public typealias ExtendedGraphemeClusterLiteralType = StringLiteralType
    public typealias UnicodeScalarLiteralType = Character
    public typealias FloatLiteral = Double
    public init (stringLiteral s: String) { self.init(s) }
    public init (extendedGraphemeClusterLiteral s: ExtendedGraphemeClusterLiteralType) { self.init(stringLiteral:s) }
    public init (unicodeScalarLiteral s: UnicodeScalarLiteralType) { self.init(stringLiteral:"\(s)") }
    
}

extension Integer : Comparable {
    
    static public func == (lhs: Integer, rhs: Integer) -> Bool { return lhs.isEqual(rhs) }
    static public func < (lhs: Integer, rhs: Integer) -> Bool { return lhs.cmp(rhs) == -1 }
}

extension Integer : Hashable {
    
    public func hash(into hasher: inout Hasher) {
//        let shift = Int(Integer.shift)
//        let mask = Int(Integer.mask)
//        var x : Int = 0
//        for n in digit.reversed() {
//            x = ((x << shift) & ~mask) | ((x >> (32-shift)) & mask)
//            x += Int(n)
//        }
//        if negative { x = -x }
//        if x == -1 { x = -2 }
        hasher.combine(digit)
        hasher.combine(negative)
    }
    
}

extension Integer : ExpressibleByIntegerLiteral {

    public init(integerLiteral value: Int) { self.init(value) }

}

extension Integer : SignedNumeric {
    
    /* ******************************************************* */
    /*  SignedNumeric compliance                               */
    
    public var magnitude: Integer { return abs() }
    public typealias Magnitude = Integer
    
    public init<T>(exactly value: T) where T : BinaryInteger {
        let maxDigits = (MemoryLayout<T>.size*8+Int(Integer.shift)-2) / Int(Integer.shift)
        var lvalue = value
        var i = 0
        
        if value == 0 { self.init(); return }
        self.init(size: maxDigits, negative: value < 0)
        if value < 0 {
            let newValue = lvalue.magnitude
            let b = T.Magnitude(Integer.base)
            let x = newValue.quotientAndRemainder(dividingBy: b)
            digit[0] = Digit(x.remainder)
            lvalue = T(x.quotient)
            i = 1
        }
        
        /* extract the digits */
        let base = T(Integer.base)
        while lvalue != 0 {
            let x = lvalue.quotientAndRemainder(dividingBy: base)
            digit[i] = Digit(x.remainder)
            lvalue = x.quotient
            i += 1
        }
        digit.removeSubrange(i..<maxDigits)  // normalize number
    }
    
    private func negate() -> Integer {
        var z = self
        z.negative = !negative
        return z
    }
    
    static public func *= (a: inout Integer, b: Integer) { a = a * b }
    
    static public prefix func - (a: Integer) -> Integer { return a.negate() }
    static public postfix func -- (a: inout Integer) { a = a - 1 }
    static public func -= (a: inout Integer, b: Integer) { a = a - b }
    
    static public prefix func + (a: Integer) -> Integer { return a }
    static public postfix func ++ (a: inout Integer) { a = a + 1 }
    static public func += (a: inout Integer, b: Integer) { a = a + b }
    
    static public func * (lhs: Integer, rhs: Integer) -> Integer { return lhs.mul(rhs) }
    static public func + (lhs: Integer, rhs: Integer) -> Integer { return lhs.add(rhs) }
    static public func - (lhs: Integer, rhs: Integer) -> Integer { return lhs.add(-rhs) }
    
}

extension Integer : BinaryInteger {
    
    public static var isSigned: Bool { return true }
    public typealias Words = [UInt]
    public var bitWidth: Int { return digit.count*Int(Integer.shift) }
    public var trailingZeroBitCount: Int {
        let x = digit.reduce(0) { (result, digit) -> Int in
            return result + digit.trailingZeroBitCount
        }
        return x
    }
    public var words : Words {
        return digit.map({ (digit) -> UInt in
            return UInt(digit)
        })
    }
    
    public init<T>(_ source: T) where T : BinaryInteger {
        self.init(exactly: source)
    }
    
    public init<T>(_ source: T) where T : BinaryFloatingPoint {
        var x = source.rounded(.towardZero)  // truncate any decimals
        let sign = x.sign
        if sign == .minus { x.negate() }
        self.init()
        
        var int = Integer.zero
        let scale = 1 << 31
        var iscale = Integer.one
        while x > 0 {
            let rem = x.truncatingRemainder(dividingBy: T(scale))
            x = (x - rem) / T(scale)
            int += iscale * Integer(Int(rem))
            iscale *= Integer(scale)
        }
        self = sign == .minus ? -int : int
    }
    
    public init<T>(clamping source: T) where T : BinaryInteger {
        self.init(exactly: source)
    }
    
    public init?<T>(exactly source: T) where T : BinaryFloatingPoint {
        guard source.exponent > 0 && 50 >= source.significandWidth, source.isNormal, source.isFinite else { return nil }
        self.init(source)
    }
    
    public init<T>(truncatingIfNeeded source: T) where T : BinaryInteger {
        self.init(exactly: source)
    }
    
    static public func % (lhs: Integer, rhs: Integer) -> Integer { return lhs.mod(rhs) }
    public static func %= (lhs: inout Integer, rhs: Integer) { lhs = lhs % rhs }
    
    static public func / (lhs: Integer, rhs: Integer) -> Integer { return lhs.div(rhs) }
    static public func /= (a: inout Integer, b: Integer) { a = a / b }
    
    static public func & (a: Integer, b: Integer) -> Integer { return a.and(b) }
    public static func &= (lhs: inout Integer, rhs: Integer) { lhs = lhs & rhs }
    public static func |= (lhs: inout Integer, rhs: Integer) { lhs = lhs | rhs }
    public static func ^= (lhs: inout Integer, rhs: Integer) { lhs = lhs ^ rhs }
    
    
    static public func | (a: Integer, b: Integer) -> Integer { return a.or(b) }
    static public func ^ (a: Integer, b: Integer) -> Integer { return a.xor(b) }
    static public prefix func ~ (a: Integer) -> Integer { return a.invert() }
    
    static public func << (a: Integer, b: Int) -> Integer { return a.lShift(b) }
    static public func >> (a: Integer, b: Int) -> Integer { return a.rShift(b) }
    public static func <<= <RHS>(lhs: inout Integer, rhs: RHS) where RHS : BinaryInteger { lhs = lhs.lShift(Int(rhs)) }
    public static func >>= <RHS>(lhs: inout Integer, rhs: RHS) where RHS : BinaryInteger { lhs = lhs.rShift(Int(rhs)) }
    
}

