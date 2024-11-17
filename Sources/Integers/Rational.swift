
//
//  Rational number implementation based on the Integer data type.
//
//  Created by Mike Griebling on 31 Jul 2015.
//  Copyright © 2015-2022 Computer Inspirations. All rights reserved.
//
public struct Rational : Codable, Sendable, Hashable {
    
    /// numerator & denominator
    let n, d : Integer
    
    public init(numerator num: Integer = Integer.zero, denominator den:Integer = Integer.one) {
        assert(!den.isZero, "Denominator = 0!")
        if den.isNegative {
            (n, d) = Self.normalize(-num, -den)
        } else {
            (n, d) = Self.normalize(num, den)
        }
    }
    
    init(_ a: (Integer, Integer)) { self.init(numerator: a.0, denominator: a.1) }
    
    public init(_ s: String) {
        let parts = s.components(separatedBy: "/")
        if parts.count == 0 { self.init() }  // zero
        else if parts.count == 1 { self.init(numerator: Integer(parts.first!)) }
        else { self.init(numerator:Integer(parts.first!), denominator: Integer(parts.last!)) }
    }
    
    static func normalize (_ n: Integer, _ d: Integer) -> (Integer, Integer) {
        let gcd = n.gcd(d)
        if gcd != 1 { return (n / gcd, d / gcd) }
        return (n, d)
    }
    
    func normalize (_ n: Integer, _ d: Integer) -> Self { Self(Self.normalize(n, d)) }
    
    func isEqual (_ n: Self) -> Bool { self.n == n.n && self.d == n.d }
    
    /// a/b < c/d => ad < bc
    func isLessThan (_ n: Self) -> Bool { self.n * n.d < self.d * n.n }
    
    /// a/b + c/d = (ad + bc) / bd
    func add (_ b: Self) -> Self { normalize(n * b.d + b.n * d, d * b.d) }
    
    /// a/b * c/d = ac/bd
    func mul (_ b: Self) -> Self { normalize(n * b.n, d * b.d) }

    func div (_ b: Self) -> Self { self.mul(b.reciprocal) }
    
    /// (a/b)^n = a^n / b^n
    func power (_ n: Integer) -> Self { Self(numerator:self.n ** n, denominator:self.d ** n) }
    
	var reciprocal : Self { Self(numerator: d, denominator: n) }
	var negate : Self { Self(numerator: -n, denominator: d) }
	var abs    : Self { Self(numerator: n.abs, denominator: d) }
    
    static public func ** (base: Self, power: Integer) -> Self { base.power(power) }
    
}

extension Rational : SignedNumeric {
    
    public init<T>(exactly source: T) where T : BinaryInteger { self.init(numerator:Integer(source)) }
    
    static public prefix func - (a: Self) -> Self { a.negate }
    static public func * (lhs: Self, rhs: Self) -> Self { lhs.mul(rhs) }
    static public func + (lhs: Self, rhs: Self) -> Self { lhs.add(rhs) }
    static public func - (lhs: Self, rhs: Self) -> Self { lhs.add(-rhs) }
    static public func / (lhs: Self, rhs: Self) -> Self { lhs.div(rhs) }
    
    static public func -= (a: inout Self, b: Self) { a = a - b }
//    static public prefix func + (a: Self) -> Self  { a }
//    static public func += (a: inout Self, b: Self) { a = a + b }
    static public func *= (a: inout Self, b: Self) { a = a * b }
    static public func /= (a: inout Self, b: Self) { a = a / b }
    
    public var magnitude: Self { self.abs }
}

extension Rational : Comparable {
    static public func == (lhs: Self, rhs: Self) -> Bool { lhs.isEqual(rhs) }
    static public func < (lhs: Self, rhs: Self) -> Bool  { lhs.isLessThan(rhs) }
}

extension Rational : ExpressibleByIntegerLiteral {
	public init(integerLiteral value: StaticBigInt) { self.init(numerator:Integer(integerLiteral: value)) }
}

extension Rational : CustomStringConvertible {
    public var description: String { d == 1 ? n.description : "\(n)/\(d)" }
}

extension Rational : ExpressibleByStringLiteral {
    public init (stringLiteral s: String) { self.init(s) }
}
