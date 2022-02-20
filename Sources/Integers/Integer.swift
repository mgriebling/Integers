import Foundation

/// Implements integer values of arbitrary magnitude.
/// This module is a reformulation of (parts of) Python's *longobject.c*
/// in Swift.  Optimizations include string optimizations for conversion
/// for power of two bases.  All errors are mine, of course.
/// Added algorithms are from Knuth: *The Art Of Computer Programming*,
/// Vol 2, section 4.3.1.
///
/// Original Oberon-2 source copyright © 2002, 2003, 2015 Michael van Acken
/// and Michael Griebling
/// Ported to Swift by Michael Griebling, 18 July 2015.
/// Swift source copyright © 2015 - 2022 Michael Griebling
///
/// This module is free software; you can redistribute it and/or
/// modify it under the terms of the GNU Lesser General Public License
/// as published by the Free Software Foundation; either version 2 of
/// the License, or (at your option) any later version.
///
/// This module is distributed in the hope that it will be useful, but
/// WITHOUT ANY WARRANTY; without even the implied warranty of
/// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
/// Lesser General Public License for more details.
///
/// You should have received a copy of the GNU Lesser General Public
/// License along with Integers. If not, write to the Free Software Foundation,
/// 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
///
public struct Integer : Codable {
    
    /// Basic data type representing one *Digit* of the *Integer*.
    public typealias Digit = Int32
    fileprivate typealias TwoDigits = Int64
    
    /// Number of bits in a *Digit*.  Minimum is 6.
    static public let shift : Digit = 30
    
    /// Modulo base of a *Digit* = 2^shift
    fileprivate static let base : Digit = 1 << shift
    fileprivate static let mask : Digit = base - 1
    
    static public let defaultDigits = 50
    
    static let factInterval = 50    // Factorial table interval
    static let factEnd = 1000       // End of factorial table
    
    /* For exponentiation, use the binary left-to-right algorithm
     * unless the exponent contains more than FIVEARY_CUTOFF digits.
     * In that case, do 5 bits at a time.  The potential drawback is that
     * a table of 2**5 intermediate results is computed.
     */
    static let FIVEARY_CUTOFF = 8
    
    /// Stores an integer number of arbitrary size.  The absolute value of a
    /// number is equal to *∑ digit[i]\*2^(shift\*i)* for 0 ≤ *i* < *size* where
    /// *size* = `digit.count`.  Negative numbers are represented
    /// with *negative = true*, and zero by *size* = 0.  In a
    /// normalized number, *digit[size-1]* (the most significant digit) is never zero.
    /// For all valid *i*, *0 ≤ digit[i] ≤ mask*.  */
    fileprivate var digit: [Digit]
    fileprivate var negative: Bool
    
    static public let zero = Integer()
    static public let one = Integer(1)
    
    /// Creates an Integer composed of *size* *Digit*s where each *Digit* holds
    /// 30 bits or around 9 decimal digits.
    public init (size : Int = 0, negative: Bool = false) {
        digit = [Digit](repeating: 0, count: size)
        self.negative = negative
    }
    
    /// Creates an Integer from a string with user-definable radix from 2 to 36.
    /// Alphabetic characters are used for radices from 11 to 36 as "A" to "Z".
    public init (_ str: String, withBase: Int) {
        self.init()
        self = Integer.fromString(str, inputBase: withBase)
    }
    
    /// Creates an Integer with the value *int*.
    public init (_ int : Int) { self.init(exactly: int) }
    
    /// Creates an Integer from a string with base 10 as a default.
    /// Prefixes of "0x", "0b", "0o" allow hexadecimal, binary, and octal inputs, respectively.
    public init (_ str: String) {
        func hasPrefix (_ s: String) -> Bool { str.hasPrefix("-"+s) || str.hasPrefix(s) }
        
        let s = str.trimmingCharacters(in: CharacterSet.whitespaces)
        if      hasPrefix("0x") { self.init(s.replacingOccurrences(of: "0x", with: ""), withBase: 16) }
        else if hasPrefix("0o") { self.init(s.replacingOccurrences(of: "0o", with: ""), withBase: 8) }
        else if hasPrefix("0b") { self.init(s.replacingOccurrences(of: "0b", with: ""), withBase: 2) }
        else { self.init(s, withBase: 10) }
    }
    
    func isEqual (_ n: Integer) -> Bool { digit == n.digit && negative == n.negative }
    
    fileprivate static func normalize(_ a: inout Integer) {
        let size = a.digit.count
        var i = size
        while i != 0 && a.digit[i-1] == 0 { i -= 1 }
        
        // remove leading zeros
        if i != size { a.digit.removeSubrange(i..<size) }
    }
    
    /// Adds the absolute values of two integers.
    fileprivate static func addAbs (_ a: Integer, b: Integer) -> Integer {
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
        normalize(&z)
        return z
    }
    
    public var isZero : Bool     { digit.count == 0 }
    public var isNegative : Bool { negative }
    public var sign : Int        { negative ? -1 : isZero ? 0 : 1 }
    
    public func abs() -> Integer { negative ? -self : self }
    
    /// Returns a *Int* approximation of *self* where
    /// very small/large values may return *Int.min* or *Int.max*, respectively.
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
    
    /// Returns a double approximation of *self*.  If *self* is too large,
    /// infinity is returned.
    public var double : Double {
        let (x, e) = scaledDouble()
        if e > Int(Int32.max / Integer.shift) { return Double.infinity }
        return ldexp(x, Int32(e) * Integer.shift)
    }
    
    /// Returns a mantissa *x* and exponent *e* approximation of *self*,
    /// *self* = x \* 2^e
    public func scaledDouble() -> (x: Double, e: Int) {
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
        assert(x > 0, "\(#function): x <= 0")
        return (x: negative ? -x : x, e: i)
    }
    
    /// Compares *self* to *b* and returns -1, 0, 1 for the cases where
    /// self < b, self = b, and self > b, respectively.
    public func cmp (_ b: Integer) -> Int {
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
    
    /// Subtract the absolute value of two integers.
    fileprivate static func subAbs (_ a: Integer, b: Integer) -> Integer {
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
        assert(borrow == 0, "\(#function): borrow != 0")
        normalize(&z)
        return z
    }
    
    /// Grade school multiplication, ignoring the signs.
    /// Returns: The absolute value of the product of *a* and *b*.
    fileprivate static func mulAbs (_ a: Integer, b: Integer) -> Integer {
        if a == b {
            return a.sqr()  // about twice as fast
        } else {
            var carry: TwoDigits
            let sizeA = a.digit.count
            let sizeB = b.digit.count
            var z = Integer(size:sizeA+sizeB)
            
            for i in 0..<sizeA {
                let f = TwoDigits(a.digit[i])
                carry = 0
                for j in 0..<sizeB {
                    carry += TwoDigits(z.digit[i+j]) + TwoDigits(b.digit[j]) * f
                    assert(carry >= 0, "\(#function): carry < 0")
                    z.digit[i+j] = Digit(carry & TwoDigits(mask))
                    carry >>= TwoDigits(shift)
                }
                var j = sizeB
                while carry != 0 {
                    carry += TwoDigits(z.digit[i+j])
                    assert(carry >= 0, "\(#function): carry < 0")
                    z.digit[i+j] = Digit(carry & TwoDigits(mask))
                    carry >>= TwoDigits(shift)
                    j += 1
                }
            }
            normalize(&z)
            return z
        }
    } // MulAbs;
    
    /// Add *self* to *b* and return the sum.
    /// Note: Subtraction is performed by *self.add(b.negate())*.
    public func add (_ b: Integer) -> Integer {
        if negative {
            if b.negative {
                var z = Integer.addAbs(self, b:b)
                z.negative = true
                return z
            } else {
                return Integer.subAbs(b, b:self)
            }
        } else {
            return b.negative ? Integer.subAbs(self, b:b) : Integer.addAbs(self, b:b)
        }
    }
    
    public func mul (_ b: Integer) -> Integer {
        var z = Integer.mulAbs(self, b:b)
        if negative != b.negative { z.negative = !z.negative }
        return z
    }
    
    /// Divide *pin*, with *size* digits, by non-zero digit
    /// *n*, storing the quotient in *pout*, and returning the remainder.
    /// *pin[0]* and *pout[0]* point at the LSD.  It's OK for
    /// *pin=pout* on entry, which saves oodles of mallocs/frees in
    /// Integer format, but that should be done with great care since Integers are
    /// immutable.
    fileprivate static func inplaceDivRem1 (_ pout: inout [Digit], pin: [Digit], psize: Int, n: Digit) -> Digit {
        assert(n > 0 && n < base, "\(#function): assertion failed")
        var rem: TwoDigits = 0
        for size in (0..<psize).reversed() {
            rem = (rem << TwoDigits(shift)) | TwoDigits(pin[size])
            let hi = rem / TwoDigits(n)
            pout[size] = Digit(hi)
            rem -= hi * TwoDigits(n)
        }
        return Digit(rem)
    } // InplaceDivRem1;
    
    /// Divide a long integer *a* by a digit *n*, returning both the quotient
    /// (as function result) and the remainder *rem*.
    /// The sign of *a* is ignored; *n* should not be zero.
    fileprivate static func divRem (_ a: Integer, n: Digit, rem: inout Digit) -> Integer {
        assert(n > 0 && n < base, "\(#function): assertion failed")
        let size = a.digit.count
        var z = Integer(size: size)
        rem = inplaceDivRem1(&z.digit, pin:a.digit, psize:size, n:n)
        normalize(&z)
        return z
    }
    
    /// Multiply by a single digit *n* and add a single digit *add*, ignoring the sign.
    fileprivate static func mulAdd (_ a: inout Integer, n: Digit, add: Digit) {
        let sizeA = a.digit.count
        var z = Integer(size:sizeA+1)
        var carry = TwoDigits(add)
        for i in 0..<sizeA {
            carry += TwoDigits(a.digit[i]) * TwoDigits(n)
            z.digit[i] = Digit(carry & TwoDigits(mask))
            carry >>= TwoDigits(shift)
        }
        z.digit[sizeA] = Digit(carry)
        normalize(&z)
        a = z
    }
    
    /// Unsigned long division with remainder
    fileprivate static func divRemAbs (_ v1: Integer, w1: Integer, rem: inout Integer) -> Integer {
        let sizeW = w1.digit.count
        let d = Digit(TwoDigits(base) / TwoDigits(w1.digit[sizeW-1]+1))
        var v = v1, w = w1
        mulAdd(&v, n:d, add:0)
        mulAdd(&w, n:d, add:0)
        
        assert(v1.digit.count >= sizeW && sizeW > 1, "\(#function): assertion 1 failed")
        assert(sizeW == w.digit.count, "\(#function): assertion 2 failed")
        
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
                assert(carry == -1, "\(#function): carry != -1")
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
        normalize(&a)
        var dx : Digit = 0
        rem = divRem(v, n:d, rem:&dx)
        return a
    } // DivRemAbs;
    
    public static func divRem (_ a: Integer, b: Integer) -> (div:Integer, mod: Integer) {
        var remDigit: Digit
        var rem, z: Integer
        
        let sizeA = a.digit.count
        let sizeB = b.digit.count
        
        assert(sizeB != 0, "\(#function): Divisor is zero") 
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
    
    @inlinable func divMod (_ w: Integer) -> (div: Integer, mod: Integer) { Integer.divRem(self, b:w) }
    
    @inlinable func div (_ w: Integer) -> Integer {
        let (div, _) = self.divMod(w)
        return div
    } // Div;
    
    @inlinable func mod (_ w: Integer) -> Integer {
        let (_, mod) = self.divMod(w)
        return mod
    } // Mod;
    
    /** Convert an *Integer* object to a string, using a given conversion base.  */
    public func description (_ outputBase: Int) -> String {
        var str = ""
        let sizeA = self.digit.count
        assert(outputBase >= 2 && outputBase <= 36, "\(#function): 2 ≤ base ≤ 36")
        
        if sizeA == 0 {
            return "0"
        } else if outputBase & (outputBase-1) == 0 {
            // special case where radix is power of two
            let baseBits = outputBase.trailingZeroBitCount
            let mask = TwoDigits(outputBase - 1)
            var accum: TwoDigits = 0
            var accumBits = TwoDigits(0)
            
            for i in 0..<sizeA {
                accum |= TwoDigits(digit[i]) << accumBits
                accumBits += TwoDigits(Integer.shift)
                assert(accumBits >= baseBits, "\(#function): Failed power of two check")
                repeat {
                    let d = Int(accum & mask)
                    assert(d >= 0, "\(#function): d < 0")
                    let c = Integer.baseDigits[d]
                    str = String(c) + str
                    accumBits -= TwoDigits(baseBits)
                    accum = accum >> TwoDigits(baseBits)
                } while !((accumBits < baseBits) && (i < sizeA-1) || (accum == 0))
            }
        } else {
            /* powbase <- largest power of outputBase that fits in a Digit. */
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
                var rem = Integer.inplaceDivRem1(&scratch.digit, pin:scratch.digit, psize:size, n:Digit(powbase))
                if scratch.digit[size-1] == 0 { size -= 1 }
                
                /* Break rem into digits. */
                assert(ntostore > 0, "\(#function): ntostore <= 0")
                repeat {
                    let nextrem = rem / Digit(outputBase)
                    let d = rem - nextrem * Digit(outputBase)
                    assert(d >= 0, "(\(#function) d < 0")
                    let c = Integer.baseDigits[Int(d)]
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
    }
    
    /// Converts a string *str* to an Integer using digits from the *inputBase*.
    static public func fromString (_ str: String, inputBase: Int) -> Integer {
        assert(2 <= inputBase && inputBase <= 36, "\(#function): 2 ≤ inputBase ≤ 36")
        
        var negative = false
        
        /* uppercase and skip leading whitespace */
        var s = str.trimmingCharacters(in: .whitespacesAndNewlines).replacingOccurrences(of: "_", with: "")
        
        /* handle sign */
        if !s.isEmpty {
            if s.hasPrefix("-") {
                negative = true
                s.removeFirst()
            } else if s.hasPrefix("+") {
                s.removeFirst()
            }
        }
        
        let upperCharacter = String(baseDigits[inputBase-1])
        var z = Integer.zero
        if inputBase & (inputBase-1) == 0 {
            // handle power-of-two radices
            let bitsPerDigit = inputBase.trailingZeroBitCount
            let n = (bitsPerDigit * s.count + Int(shift) - 1) / Int(shift)  // approximately how many words we need
            z = Integer(size: n)
            var accum = TwoDigits(0)
            var bitsInAccum = 0
            var i = 0
            while !s.isEmpty {
                let c = String(s.removeLast())
                if let k = Int(c, radix: inputBase) {
                    accum |= TwoDigits(k) << bitsInAccum
                    bitsInAccum += bitsPerDigit
                    if bitsInAccum >= shift {
                        z.digit[i] = Digit(accum & TwoDigits(mask)); i+=1    // just store the required *shift* bits
                        assert(i <= n, "Not enough digits in z")
                        accum = accum >> shift
                        bitsInAccum -= Int(shift)
                        assert(bitsInAccum < shift, "Too many bits")
                    }
                } else {
                    assertionFailure("\(#function): character '\(c)' must be '0' to '\(upperCharacter)'")
                }
            }
            if bitsInAccum > 0 {
                assert(bitsInAccum <= shift, "Too many bits")
                z.digit[i] = Digit(accum); i+=1
                assert(i <= n, "Not enough digits in z")
            }
            normalize(&z)
        } else {
            // other radices like 10
            var divisors = [Int]()
            var x = 1
            for _ in 1...s.count {
                x *= inputBase
                if x > base { break }
                divisors.append(x)
            }
            while !s.isEmpty {
                var si = ""; si.reserveCapacity(divisors.count)
                for _ in 1...divisors.count where !s.isEmpty {
                    si.append(s.removeFirst())
                }
                if let d = Int(si, radix: inputBase) {
                    Integer.mulAdd(&z, n:Digit(divisors[si.count-1]), add:Digit(d))
                } else {
                    assertionFailure("\(#function): string characters \"\(si)\" must be '0' to '\(upperCharacter)'")
                }
            }
        }
        z.negative = negative
        return z
    }
    
    /// Mapping of integer to base digits so that baseDigits[10] -> "A"
    static private let baseDigits: [Character] = Array("0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ")
    
    /// Bitwise signed 1's complement.  The result equals -(a+1).
    public func invert() -> Integer {
        var a = self
        Integer.mulAdd(&a, n: 1, add: 1)
        a.negative = !negative
        return a
    }
    
    public func lShift (_ n: Int) -> Integer {
        assert(n >= 0, "\(#function): Shift is negative")
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
            assert(accum == 0, "\(#function): remShift == 0")
        }
        Integer.normalize(&z)
        return z
    } // LShift;
    
    public func rShift (_ n: Int) -> Integer {
        assert(n >= 0, "\(#function): Shift is negative")
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
                Integer.normalize(&z)
                return z
            }
        }
    } // RShift;
    
    /// Euclid's gcd algorithm  (very elegant and very ancient!)
    /// Returns greatest common divisor of *m* and *n* where *m* = *self*
    /// Precondition: m ≥ n, n > 0
    public func gcd (_ n: Integer) -> Integer {
//        assert(!self.isNegative && !n.isNegative, "\(#function): m < 0 or n < 0")
        var x = self.abs()
        var y = n.abs()
        
        /* To start everything must be non-negative and x >= y */
        if x < y { swap(&x, &y) }  // swap x and y so that x >= y
        
        while !y.isZero {
            let xmody=x.mod(y)    /* division algorithm */
            x=y; y=xmody          /* set up next iteration */
        }
        return x
    }
    
    /// Returns x^b where x = *self*.
    /// Precondition: b ≥ 0
    public func power (_ b: Integer) -> Integer {
        guard b>=0 else { return Integer.zero }  /* x**-exp = 0 */
        var x = self
        var y = Integer.one
        if self.digit.count <= Integer.FIVEARY_CUTOFF {
            // use the straight-forward algorithm (HAC Algorithm 14.79)
            var lexp = b
            while lexp > 0 {
                if !lexp.isMultiple(of: 2) { y*=x }
                lexp >>= 1
                if lexp > 0 { x=x.sqr() }
            }
        } else {
            // Left-to-right 5-ary exponentiation (HAC Algorithm 14.82)
            var table = [Integer](); table.reserveCapacity(32)
            table.append(y)
            for i in 1..<32 { table.append(table[i-1] * x) }
        
            for i in stride(from: b.digit.count-1, through: 0, by: -1) {
                let bi = b.digit[i]
                for j in stride(from: Integer.shift-5, through: 0, by: -5) {
                    let index = Int((bi >> j)) & 0x1F
                    for _ in 0..<5 { y = y.sqr() }
                    if index != 0 { y = y * table[index] }
                }
            }
        }
        return y
    }
    
    /// Returns x^2 where x = *self*.
    /// This method requires around half the operations of x \* x.
    /// Using algorithm 14.16 from *Handbook of Applied Cryptography*.
    public func sqr () -> Integer {
        typealias Digit2 = Integer.TwoDigits
        let digits = self.digit.count
        let mask = Integer.TwoDigits(Integer.mask)
        var w = Integer(size:digits*2)
        let x = self.digit
        for i in 0..<digits {
            let xi = Digit2(x[i])
            var uv = Digit2(w.digit[2*i])+xi*xi
            w.digit[2*i] = Integer.Digit(uv & mask)
            var c = uv >> Integer.shift
            for j in (i+1)..<digits {
                uv = Digit2(w.digit[i+j]) + 2*Digit2(x[j])*xi + c
                w.digit[i+j] = Integer.Digit(uv & mask)
                c = uv >> Integer.shift
            }
            w.digit[i+digits] = Digit(c)
        }
        Integer.normalize(&w)
        return w
    }
    
    /// Returns the integral square root of *self* using Newton's algorithm.
    public func sqrt() -> Integer {
        guard !self.isNegative || self.isZero else { return Integer.zero }
        var t1, t2: Integer
        
        /* First approx */
        let sqrtx = self.double.squareRoot()
        t1 = Integer(sqrtx)
        
        /* t1 > 0  */
        t2 = self / t1
        t1 = t2 + t1
        t1 = t1 >> 1
        
        /* And now t1 > sqrt(arg) */
        repeat {
            t2 = self / t1
            t1 = t1 + t2
            t1 = t1 >> 1
        } while t1 > t2
        return t1
    }
    
    /// Small primes under 2000 -- sequence A00040 in the OEIS
    static let smallPrimes = [
           2,   3,    5,    7,   11,    13,   17,   19,   23,   29,   31,   37,   41,   43,   47,   53,   59,   61,   67,   71,
          73,  79,   83,   89,   97,   101,  103,  107,  109,  113,  127,  131,  137,  139,  149,  151,  157,  163,  167,  173,
         179,  181,  191,  193,  197,  199,  211,  223,  227,  229,  233,  239,  241,  251,  257,  263,  269,  271,  277,  281,
         283,  293,  307,  311,  313,  317,  331,  337,  347,  349,  353,  359,  367,  373,  379,  383,  389,  397,  401,  409,
         419,  421,  431,  433,  439,  443,  449,  457,  461,  463,  467,  479,  487,  491,  499,  503,  509,  521,  523,  541,
         547,  557,  563,  569,  571,  577,  587,  593,  599,  601,  607,  613,  617,  619,  631,  641,  643,  647,  653,  659,
         661,  673,  677,  683,  691,  701,  709,  719,  727,  733,  739,  743,  751,  757,  761,  769,  773,  787,  797,  809,
         811,  821,  823,  827,  829,  839,  853,  857,  859,  863,  877,  881,  883,  887,  907,  911,  919,  929,  937,  941,
         947,  953,  967,  971,  977,  983,  991,  997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069,
        1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223,
        1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373,
        1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511,
        1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657,
        1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811,
        1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987,
        1993, 1997, 1999
    ]
    
    enum MillerRabinError: Error {
        case primeLowAccuracy
        case primeLowerBorder
        case uIntOverflow
    }
    
    /** Calculates the modular exponentiation based on `Applied Cryptography by Bruce Schneier.`
     in `Schneier, Bruce (1996). Applied Cryptography: Protocols, Algorithms,
     and Source Code in C, Second Edition (2nd ed.). Wiley. ISBN 978-0-471-11709-4.`

     - Parameter base: The natural base b.
     - Parameter base: The natural exponent e.
     - Parameter base: The natural modulus m.
     - Returns: The modular exponentiation c.
    */
    private func calculateModularExponentiation(base: Integer, exponent: Integer, modulus: Integer) -> Integer {
        guard modulus > 1 else { return 0 }

        var result: Integer = 1
        var exponentCopy = exponent
        var baseCopy = base % modulus

        while exponentCopy > 0 {
            if exponentCopy % 2 == 1 {
                result = (result * baseCopy) % modulus
            }
            exponentCopy = exponentCopy >> 1
            baseCopy = (baseCopy * baseCopy) % modulus
        }

        return result
    }
    
    /** The Miller–Rabin test relies on an equality or set of equalities that
     hold true for prime values, then checks whether or not they hold for
     a number that we want to test for primality.

     - Parameter n: an odd integer to be tested for primality;
     - Parameter k: a parameter that determines the accuracy of the test
     - throws: Can throw an error of type `MillerRabinError`.
     - Returns: composite if n is composite, otherwise probably prime
    */
    public func isPrime(accuracy k: UInt = 1) throws -> Bool {
        let n = self
        guard k > 0 else { throw MillerRabinError.primeLowAccuracy }
        guard n > 0 else { throw MillerRabinError.primeLowerBorder }
        guard n > 3 else { return true }

        // return false for all even numbers bigger than 2
        if n % 2 == 0 { return false }
        let s = (n - 1).trailingZeroBitCount
        let d = (n - 1) >> s
        guard 2 ** s * d == n - 1 else { throw MillerRabinError.primeLowerBorder }
        
        /// Inspect whether a given witness will reveal the true identity of n.
        func tryComposite(_ a: Integer, d: Integer, n: Integer) -> Bool? {
            var x = calculateModularExponentiation(base: a, exponent: d, modulus: n)
            if x == 1 || x == (n - 1) {
                return nil
            }
            for _ in 1..<s {
                x = calculateModularExponentiation(base: x, exponent: 2, modulus: n)
                if x == 1 {
                    return false
                } else if x == (n - 1) {
                    return nil
                }
            }
            return false
        }

        for _ in 0..<k {
            let a = Integer.random(2...n-3)
            if let composite = tryComposite(a, d: d, n: n) {
                return composite
            }
        }

        return true
    }
    
    /// Returns x! = x(x-1)(x-2)...(2)(1) where *x* = *self*.
    /// Precondition: *x* ≥ 0
    public func factorial () -> Integer {
        assert(!self.isNegative, "\(#function): x must be ≥ 0!")
        let x = self.integer
        if x < 0 { return Integer.zero }  /* out of range */
        if x < 2 { return Integer.one }   /* 0! & 1! */
        
        var f = Integer.one
        var start = Digit(2)
        let factInt = Integer.factInterval
        if x > factInt && x <= Integer.factEnd {
            let index = (x - factInt) / factInt
            f = Integer.factTable[index]
            start = Digit(index * factInt + factInt+1)
            if start > x { return f }
        }

        for lx in start...Digit(x) {
            Integer.mulAdd(&f, n: lx, add: 0)  /* f=f*x */
        }
        Integer.normalize(&f)
        return f
    }
    
    // Table of factorials at every 50 steps to 1000
    static private var factTable : [Integer] = {
        var facts = [Integer]()
        var f = Integer.one
        for lx in 2...Digit(Integer.factEnd) {
            Integer.mulAdd(&f, n: lx, add: 0)  /* f=f*x */
            if lx.isMultiple(of: Digit(Integer.factInterval)) {
                var s = f
                Integer.normalize(&s)
                facts.append(s)
            }
        }
        return facts
    }()
    
    ///  log(10) / log(2)
    static let log10overLog2 = 3.321928095
    
    /// Returns the number of Digits needed to hold *decimalDigits*.
    static func toDigits(decimalDigits:Int) -> Int {
        let ndigits = log10overLog2 / Double(shift)                       // number of Digits per base 10 digit
        return Swift.max(1,Int(round(Double(decimalDigits)*ndigits+0.5))) // n size = digits*log(10)/log(2)
    }
    
    /// Returns the number of Digits needed to hold *decimalDigits*.
    static func toDigits(decimalDigits:Integer) -> Int {
        let ndigits = log10overLog2 / Double(shift)                       // number of Digits per base 10 digit
        return Swift.max(1,Int(round(Double(decimalDigits)*ndigits+0.5))) // n size = digits*log(10)/log(2)
    }
    
    static func toDecimalDigits(digits:Int) -> Int {
        let ndigits = Double(shift) / log10overLog2     // number of base 10 digits per Digit
        return Swift.max(1,Int(round(Double(digits)*ndigits+0.5))) // n size = digits*log(2)/log(10)
    }
    
    /// Returns a random number within the specified *range*.
    public static func random (_ range:ClosedRange<Integer>) -> Integer {
        let digits = range.upperBound.digit.count
        let size = Int.random(in: 1...digits)  // pick a random size
        let number = Integer.random(digits:toDecimalDigits(digits:size)) % (range.upperBound+1)
        if number < range.lowerBound { return number+range.lowerBound }
        return number
    }
    
    // Returns a random number exactly *bits* in length.
    public static func random (bits: Int) -> Integer {
        let B = Int(mask)
        let BPD = Int(shift)       // bits per Digit
        let digits = bits / BPD    // number of Digits in result
        
        // create the random Digits
        var n = Integer(size: digits+1)
        for i in 0...digits { n.digit[i] = Digit(Int.random(in: 0..<B)) }
        
        // drop any unneeded bits
        let actual = n.bitWidth - n.leadingZeroBitCount
        let delta = actual - bits
        if delta > 0 { return n >> delta }
        return n << (-delta) | Integer(Int.random(in: 0...1))
    }
    
    /// Returns a decimal *digits*-length random number.
    /// Default length for digits is 50.
    public static func random (digits: Int = defaultDigits) -> Integer {
        let B = mask
        let udigits = digits <= 0 ? defaultDigits : digits
        var n = Integer(size: toDigits(decimalDigits: udigits))

        // create the random Digits
        for i in 0..<n.digit.count { n.digit[i] = Digit(Int.random(in: 0..<Int(B))) }
        
        // adjust the size to decimal digit places
        let aDigits = toDecimalDigits(digits: n.digit.count)
        if aDigits > udigits { n /= 10 ** (aDigits - udigits) }
        return n
    }
    
    /* ******************************************************* */
    /*  Logical operations                                     */
    
    /// Returns an extension of self to *size* digits.
    fileprivate func extendedTo (_ size: Int) -> Integer {
        if digit.count == size { return self }
        var y = Integer(size: size)
        y.negative = negative
        y.digit[0..<digit.count] = digit[0..<digit.count]
        return y
    }
    
    /// Creates a limited *size* unsigned version of *self*.
    fileprivate func unsigned (_ size: Int) -> Integer {
        if !negative { return self.extendedTo(size) }
        var a = Integer(size: size)
        
        /* convert to 1's complement */
        let b = (self+1).extendedTo(size)
        for i in 0..<size { a.digit[i] = ~b.digit[i] & Integer.mask }
        return a
    }
    
    /// Creates a normalized signed version of *z*.
    fileprivate static func signed (_ z: inout Integer) {
        let size = z.digit.count
        let signMask = Digit(1 << (shift-1))   // sign bit mask
        if size == 0 { return }
        z.negative = z.digit[size-1] & signMask != 0
        
        // convert back to two's complement format
        if z.negative {
            for i in 0..<size { z.digit[i] = ~z.digit[i] & Integer.mask }
            z-=1
        }
        normalize(&z)
    }
    
    /// Returns *op()* applied to *self* and *y*.
    public func lop (_ y: Integer, op: (Digit, Digit) -> Digit) -> Integer {
        let size = Swift.max(digit.count, y.digit.count)
        let a = self.unsigned(size)
        let b = y.unsigned(size)
        var z = Integer(size: size)
        for i in 0..<size { z.digit[i] = op(a.digit[i], b.digit[i]) }
        Integer.signed(&z)
        return z
    }
    
    /// Returns bitwise **and** of *self* and *y*
    @inlinable func and (_ y : Integer) -> Integer { self.lop(y, op: &) }
    
    ///Returns bitwise **or** of *self* and *y*.
    @inlinable func or (_ y : Integer) -> Integer { self.lop(y, op: |) }
    
    /// Returns bitwise **xor** of *self* and *y*.
    @inlinable func xor (_ y : Integer) -> Integer { self.lop(y, op: ^) }
    
    /// Returns *self* with *bit* set in the receiver.
    @inlinable func setBit(_ bit: Int) -> Integer { self | (1 << bit) }
    
    /// Returns *self* with *bit* cleared in the receiver.
    @inlinable func clearBit(_ bit: Int) -> Integer { self & ~(1 << bit) }
    
    /// Returns *self* with *bit* toggled in the receiver.
    @inlinable func toggleBit(_ bit: Int) -> Integer { self ^ (1 << bit) }
    
    @inlinable static public func ** (base: Integer, power: Integer) -> Integer { base.power(power) }
    
}

// Definition of power operator
infix operator ** : ExponentPrecedence
precedencegroup ExponentPrecedence {
    associativity: left
    higherThan: MultiplicationPrecedence
}

@inlinable public func ** (base: Int, power: Int) -> Integer { Integer(base) ** Integer(power) }

extension Integer : CustomStringConvertible {
    public var description: String { self.description(10) }
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
    public init (stringLiteral s: String) { self.init(s) }
}

extension Integer : Comparable {
    static public func == (lhs: Integer, rhs: Integer) -> Bool { lhs.isEqual(rhs) }
    static public func < (lhs: Integer, rhs: Integer) -> Bool  { lhs.cmp(rhs) == -1 }
}

extension Integer : Hashable {
    public func hash(into hasher: inout Hasher) {
        hasher.combine(digit)
        hasher.combine(negative)
    }
}

extension Integer : ExpressibleByIntegerLiteral {
    public init(integerLiteral value: Int) { self.init(value) }
}

extension Integer : SignedInteger {
    
    @inlinable public var magnitude: Integer { abs() }
    
    /// Creates an Integer whose value is exactly equal to *value*.
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
        digit.removeLast(maxDigits-i) // normalize number
//        digit.removeSubrange(i..<maxDigits)
    }
    
    private func negate() -> Integer {
        var z = self
        z.negative = !negative
        return z
    }
    
    @inlinable static public func *= (a: inout Integer, b: Integer) { a = a * b }
    static public prefix func - (a: Integer) -> Integer             { a.negate() }
    @inlinable static public func -= (a: inout Integer, b: Integer) { a = a - b }
    
    @inlinable static public prefix func + (a: Integer) -> Integer  { a }
    @inlinable static public func += (a: inout Integer, b: Integer) { a = a + b }
    
    @inlinable static public func * (lhs: Integer, rhs: Integer) -> Integer { lhs.mul(rhs) }
    @inlinable static public func + (lhs: Integer, rhs: Integer) -> Integer { lhs.add(rhs) }
    @inlinable static public func - (lhs: Integer, rhs: Integer) -> Integer { lhs.add(-rhs) }
}

extension Integer : BinaryInteger {
    
    public static var isSigned: Bool { true }
    public typealias Words = [UInt]
    
    public var bitWidth: Int { digit.count*Int(Integer.shift) }
    public var trailingZeroBitCount: Int {
        var zeros = 0
        for dig in digit {
            if dig == 0 {
                // add full word bits
                zeros += Int(Integer.shift)
            } else {
                // add partial bits
                zeros += dig.trailingZeroBitCount
                break
            }
        }
        return zeros
    }
    public var leadingZeroBitCount: Int { digit.last?.leadingZeroBitCount ?? 0 }
    public var nonzeroBitCount: Int { digit.reduce(0) { $0 + $1.nonzeroBitCount } }
    public var isPowerOfTwo: Bool { self.nonzeroBitCount == 1 }
    
    public var words : Words { digit.map { UInt($0) } }
    public init<T>(_ source: T) where T : BinaryInteger { self.init(exactly: source) }
     
    public init<T>(_ source: T) where T : BinaryFloatingPoint {
        var x = source.rounded(.towardZero)  // truncate any decimals
        let sign = x.sign
        if sign == .minus { x.negate() }
        self.init()
        
        var int = Integer.zero
        let scale = Integer.base
        var iscale = Integer.one
        while x > 0 {
            let rem = x.truncatingRemainder(dividingBy: T(scale))
            x = (x - rem) / T(scale)
            int += iscale * Integer(Int(rem))
            iscale *= Integer(scale)
        }
        self = sign == .minus ? -int : int
    }
    
    public init<T>(clamping source: T) where T : BinaryInteger { self.init(exactly: source) }
    
    public init?<T>(exactly source: T) where T : BinaryFloatingPoint {
        guard source.exponent > 0 && 50 >= source.significandWidth, source.isNormal, source.isFinite else { return nil }
        self.init(source)
    }
    
    @inlinable public init<T>(truncatingIfNeeded source: T) where T : BinaryInteger { self.init(exactly: source) }
    
    @inlinable static public func % (lhs: Integer, rhs: Integer) -> Integer { lhs.mod(rhs) }
    @inlinable public static func %= (lhs: inout Integer, rhs: Integer) { lhs = lhs % rhs }
    
    @inlinable static public func / (lhs: Integer, rhs: Integer) -> Integer { lhs.div(rhs) }
    @inlinable static public func /= (a: inout Integer, b: Integer) { a = a / b }
    
    @inlinable static public func & (a: Integer, b: Integer) -> Integer { a.and(b) }
    @inlinable public static func &= (lhs: inout Integer, rhs: Integer) { lhs = lhs & rhs }
    @inlinable public static func |= (lhs: inout Integer, rhs: Integer) { lhs = lhs | rhs }
    @inlinable public static func ^= (lhs: inout Integer, rhs: Integer) { lhs = lhs ^ rhs }
    
    @inlinable static public func | (a: Integer, b: Integer) -> Integer { a.or(b) }
    @inlinable static public func ^ (a: Integer, b: Integer) -> Integer { a.xor(b) }
    @inlinable static public prefix func ~ (a: Integer) -> Integer { a.invert() }
    
    @inlinable static public func << (a: Integer, b: Int) -> Integer { a.lShift(b) }
    @inlinable static public func >> (a: Integer, b: Int) -> Integer { a.rShift(b) }
    @inlinable public static func <<= <RHS>(lhs: inout Integer, rhs: RHS) where RHS : BinaryInteger { lhs = lhs.lShift(Int(rhs)) }
    @inlinable public static func >>= <RHS>(lhs: inout Integer, rhs: RHS) where RHS : BinaryInteger { lhs = lhs.rShift(Int(rhs)) }
}

