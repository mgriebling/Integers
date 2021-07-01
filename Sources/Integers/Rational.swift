//
//  Rational.swift
//  Integers
//
//  Created by Mike Griebling on 31 Jul 2015.
//  Copyright © 2015 Computer Inspirations. All rights reserved.
//

import Foundation

public struct Rational : Codable, Hashable {
    
    let n : Integer  /// numerator
    let d : Integer  /// denominator
    
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
    
    fileprivate func normalize (_ n: Integer, _ d: Integer) -> Rational {
        return Rational(Rational.normalize(n, d))
    }
    
    func isEqual (_ n: Rational) -> Bool { return self.n == n.n && self.d == n.d }
    
    func isLessThan (_ n: Rational) -> Bool {
        // a/b < c/d => ad < bc
        return self.n * n.d < self.d * n.n
    }
    
    func add (_ b: Rational) -> Rational {
        // a/b + c/d = (ad + bc) / bd
        return normalize(n * b.d + b.n * d, d * b.d)
    }
    
    func mul (_ b: Rational) -> Rational {
        // a/b * c/d = ac/bd
       return normalize(n * b.n, d * b.d)
    }
    
    func reciprocal () -> Rational {
        return Rational(numerator: d, denominator: n)
    }
    
    func div (_ b: Rational) -> Rational {
        return self.mul(b.reciprocal())
    }
    
    func power (_ n: Int) -> Rational {
        // (a/b)^n = a^n / b^n
        return Rational(numerator:self.n ** n, denominator:self.d ** n)
    }
    
    func abs () -> Rational {
        return Rational(numerator: n.abs(), denominator: d)
    }
    
    func negate() -> Rational {
        return Rational(numerator: -n, denominator: d)
    }
    
    static public func ** (base: Rational, power: Int) -> Rational { return base.power(power) }
    
}

extension Rational : SignedNumeric {
    
    public typealias Magnitude = Rational
    
    public init<T>(exactly source: T) where T : BinaryInteger {
        self.init(numerator:Integer(source))
    }
    
    static public prefix func - (a: Rational) -> Rational { return a.negate() }
    
    static public func * (lhs: Rational, rhs: Rational) -> Rational { return lhs.mul(rhs) }
    static public func + (lhs: Rational, rhs: Rational) -> Rational { return lhs.add(rhs) }
    static public func - (lhs: Rational, rhs: Rational) -> Rational { return lhs.add(-rhs) }
    static public func / (lhs: Rational, rhs: Rational) -> Rational { return lhs.div(rhs) }
    
    static public func -= (a: inout Rational, b: Rational) { a = a - b }
    
    static public prefix func + (a: Rational) -> Rational { return a }
    static public func += (a: inout Rational, b: Rational) { a = a + b }
    
    static public func *= (a: inout Rational, b: Rational) { a = a * b }
    static public func /= (a: inout Rational, b: Rational) { a = a / b }
    
    public var magnitude: Rational { return self.abs() }
}

extension Rational : Comparable {

    static public func == (lhs: Rational, rhs: Rational) -> Bool { return lhs.isEqual(rhs) }
    static public func < (lhs: Rational, rhs: Rational) -> Bool { return lhs.isLessThan(rhs) }
    
}

extension Rational : ExpressibleByIntegerLiteral {
    
    public typealias IntegerLiteralType = Int
    public init(integerLiteral value: Int) {
        self.init(numerator:Integer(value))
    }

}

extension Rational : CustomStringConvertible {
 
    public var description: String {
        return d == 1 ? n.description : "\(n)/\(d)"
    }
}

extension Rational : ExpressibleByStringLiteral {
    
    public typealias ExtendedGraphemeClusterLiteralType = StringLiteralType
    public typealias UnicodeScalarLiteralType = Character
    public init (stringLiteral s: String) { self.init(s) }
    public init (extendedGraphemeClusterLiteral s: ExtendedGraphemeClusterLiteralType) { self.init(stringLiteral:s) }
    public init (unicodeScalarLiteral s: UnicodeScalarLiteralType) { self.init(stringLiteral:"\(s)") }
    
}
