import Foundation

//
//  Rational number implementation based on the Integer data type.
//
//  Created by Mike Griebling on 31 Jul 2015.
//  Copyright © 2015-2022 Computer Inspirations. All rights reserved.
//
public struct Rational : Codable, Hashable {
    
    /// numerator & denominator
    let n, d : Integer
    
    public init(numerator num: Integer = Integer.zero, denominator den:Integer = Integer.one) {
        assert(!den.isZero, "Denominator = 0!")
        if den.isNegative {
            (n, d) = Rational.normalize(-num, -den)
        } else {
            (n, d) = Rational.normalize(num, den)
        }
    }
    
    fileprivate init(_ a: (Integer, Integer)) { self.init(numerator: a.0, denominator: a.1) }
    
    public init(_ s: String) {
        let parts = s.components(separatedBy: "/")
        if parts.count == 0 { self.init() }  // zero
        else if parts.count == 1 { self.init(numerator: Integer(parts.first!)) }
        else { self.init(numerator:Integer(parts.first!), denominator: Integer(parts.last!)) }
    }
    
    fileprivate static func normalize (_ n: Integer, _ d: Integer) -> (Integer, Integer) {
        let gcd = n.gcd(d)
        if gcd != 1 { return (n / gcd, d / gcd) }
        return (n, d)
    }
    
    fileprivate func normalize (_ n: Integer, _ d: Integer) -> Rational { Rational(Rational.normalize(n, d)) }
    
    func isEqual (_ n: Rational) -> Bool { self.n == n.n && self.d == n.d }
    
    /// a/b < c/d => ad < bc
    func isLessThan (_ n: Rational) -> Bool { self.n * n.d < self.d * n.n }
    
    /// a/b + c/d = (ad + bc) / bd
    func add (_ b: Rational) -> Rational { normalize(n * b.d + b.n * d, d * b.d) }
    
    /// a/b * c/d = ac/bd
    func mul (_ b: Rational) -> Rational { normalize(n * b.n, d * b.d) }
    func reciprocal () -> Rational { Rational(numerator: d, denominator: n) }
    func div (_ b: Rational) -> Rational { self.mul(b.reciprocal()) }
    
    /// (a/b)^n = a^n / b^n
    func power (_ n: Integer) -> Rational { Rational(numerator:self.n ** n, denominator:self.d ** n) }
    func abs () -> Rational { Rational(numerator: n.abs(), denominator: d) }
    func negate() -> Rational { Rational(numerator: -n, denominator: d) }
    
    static public func ** (base: Rational, power: Integer) -> Rational { base.power(power) }
    
}

extension Rational : SignedNumeric {
    
    public init<T>(exactly source: T) where T : BinaryInteger { self.init(numerator:Integer(source)) }
    
    static public prefix func - (a: Rational) -> Rational { a.negate() }
    static public func * (lhs: Rational, rhs: Rational) -> Rational { lhs.mul(rhs) }
    static public func + (lhs: Rational, rhs: Rational) -> Rational { lhs.add(rhs) }
    static public func - (lhs: Rational, rhs: Rational) -> Rational { lhs.add(-rhs) }
    static public func / (lhs: Rational, rhs: Rational) -> Rational { lhs.div(rhs) }
    
    static public func -= (a: inout Rational, b: Rational) { a = a - b }
    static public prefix func + (a: Rational) -> Rational  { a }
    static public func += (a: inout Rational, b: Rational) { a = a + b }
    static public func *= (a: inout Rational, b: Rational) { a = a * b }
    static public func /= (a: inout Rational, b: Rational) { a = a / b }
    
    public var magnitude: Rational { self.abs() }
}

extension Rational : Comparable {
    static public func == (lhs: Rational, rhs: Rational) -> Bool { lhs.isEqual(rhs) }
    static public func < (lhs: Rational, rhs: Rational) -> Bool  { lhs.isLessThan(rhs) }
}

extension Rational : ExpressibleByIntegerLiteral {
    public init(integerLiteral value: Int) { self.init(numerator:Integer(value)) }
}

extension Rational : CustomStringConvertible {
    public var description: String { d == 1 ? n.description : "\(n)/\(d)" }
}

extension Rational : ExpressibleByStringLiteral {
    public init (stringLiteral s: String) { self.init(s) }
}
