//
//  Test.swift
//  Integers
//
//  Created by Mike Griebling on 17.11.2024.
//

import XCTest
@testable import Integers

//
//  IntegersTests.swift
//  IntegersTests
//
//  Created by Mike Griebling on 18 Jul 2015.
//  Copyright © 2015 Computer Inspirations. All rights reserved.
//

final class RationalsTests: XCTestCase {
	
	override func setUp() {
		super.setUp()
		// Put setup code here. This method is called before the invocation of each test method in the class.
	}
	
	override func tearDown() {
		// Put teardown code here. This method is called after the invocation of each test method in the class.
		super.tearDown()
	}
	
	func testRationals() {
		// This is an example of a functional test case.
		// Use XCTAssert and related functions to verify your tests produce the correct results.

		func check (_ a: String, _ n: Rational, _ m: String) {
			let pass = n.description == m
			if pass { print(a, n, " -> PASS") }
			XCTAssert(pass, "\(a)\(n) -> FAIL!")
		}
		
		func check (_ a: String, _ n: String, _ m: String) {
			let pass = n == m
			if pass { print(a, n, " -> PASS") }
			XCTAssert(pass, "\(a)\(n) -> FAIL!")
		}
		
		func check2 (_ a: String, _ n: Rational, _ m: String) {
			let pass = n.description == m
			if pass { print(a, n.description, " -> PASS") }
			XCTAssert(pass, "\(a)\(n.description) -> FAIL!")
		}
		
		check("Zero = ", Rational.zero, "0")
		let ns = "123456789012345678900000000000000000001"
		let ms = "55554444333322221111"
		var n = Rational(ns + "/" + ms)
		let m = Rational(ms + "/" + ns)
		check("n/m = ", n, "11223344455667788990909090909090909091/5050404030302020101")
		check("m/n = ", m, "5050404030302020101/11223344455667788990909090909090909091")
		let min = Rational(exactly: Int.min)
		XCTAssert("\(min)" == "\(Int.min)")
		check("n*m = ", n * m, "1")
		check("(n*m) / m = ", (n * m) / m, n.description)
		check("n+m = ", n + m, "125963460770568898761905123863652109201100907960404039687909402102234496482/56682424072372433486935481744390142627731854911845638191")
		check("n-m = ", n - m, "125963460770568898761905123863652109150087746221822263746801341699418396080/56682424072372433486935481744390142627731854911845638191")
		check("n / m = ", n / m, "125963460770568898761905123863652109175594327091113151717355371900826446281/25506580869290887970554030201408050201")
		n /= m
		check("n /= m", n, "125963460770568898761905123863652109175594327091113151717355371900826446281/25506580869290887970554030201408050201")
		n -= 10
		check("n -= 10", n, "125963460770568898761905123863652108920528518398204272011815069886745944271/25506580869290887970554030201408050201")
		n *= 11
		check("n *= 11", n, "1385598068476257886380956362500173198125813702380246992129965768754205386981/25506580869290887970554030201408050201")
		let two64 = Rational(-2) ** 64
		check("2**64 = ", two64, "18446744073709551616")
		check("-(1/8)**3 = ", Rational(numerator: 1, denominator: -8) ** 3, "-1/512")
		XCTAssert(n != m, "\(n) == \(m)")
		XCTAssert(n > m, "\(n) <= \(m)")
		XCTAssertFalse(n == m)
		XCTAssert((Rational(numerator: 1, denominator: -8) ** 3).magnitude.description == "1/512")
	}
	
	let s = "1711224524281413113724683388812728390922705448935203693936480409232572797541406474240000000000000001"
	let t = "1711224524281413113724683388812728390922705448935203693936480409232572797541406474240000000000000002"
	
	func testPerformanceFromString() {
		var x = Rational()
		self.measure {
			// Put the code you want to measure the time of here.
			for _ in 1...1000 { x = Rational("\(s)/\(t)") }
		}
		print(x)
	}
	
}


