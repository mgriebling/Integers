    import XCTest
    @testable import Integers

    //
    //  IntegersTests.swift
    //  IntegersTests
    //
    //  Created by Mike Griebling on 18 Jul 2015.
    //  Copyright © 2015 Computer Inspirations. All rights reserved.
    //

    final class IntegersTests: XCTestCase {
        
        override func setUp() {
            super.setUp()
            // Put setup code here. This method is called before the invocation of each test method in the class.
        }
        
        override func tearDown() {
            // Put teardown code here. This method is called after the invocation of each test method in the class.
            super.tearDown()
        }
        
        func testIntegers() {
            // This is an example of a functional test case.
            // Use XCTAssert and related functions to verify your tests produce the correct results.

            func check (_ a: String, _ n: Integer, _ m: String) {
                let pass = n.description == m
                if pass { print(a, n, " -> PASS") }
                XCTAssert(pass, "\(a)\(n) -> FAIL!")
            }
            
            func check (_ a: String, _ n: String, _ m: String) {
                let pass = n == m
                if pass { print(a, n, " -> PASS") }
                XCTAssert(pass, "\(a)\(n) -> FAIL!")
            }
            
            func check2 (_ a: String, _ n: Integer, _ base: Int, _ m: String) {
                let pass = n.description(base) == m
                if pass { print(a, n.description(base), " -> PASS") }
                XCTAssert(pass, "\(a)\(n.description(base)) -> FAIL!")
            }
            
            check("Zero = ", Integer.zero, "0")
            check("One = ", Integer.one, "1")
            let ns = "123456789012345678900000000000000000000"
            let ms = "55554444333322221111"
            let n = Integer(ns)
            let m = Integer(ms)
            check("n = ", n, ns)
            check("m = ", m, ms)
            let min = Integer(exactly: Int.min)
            XCTAssert("\(min)" == "\(Int.min)")
            let minf = Integer(exactly: Double.greatestFiniteMagnitude)
            XCTAssert(minf == nil, "Double.greatestFiniteMagnitude -> FAIL!")
            XCTAssertTrue(n.cmp(m) == 1, "n<=m -> FAIL!")
            check("n*m = ", n * m, "6858573312757064451919193291071207257900000000000000000000")
            check("(n*m) / m = ", (n * m) / m, ns)
            check("n+m = ", n + m, "123456789012345678955554444333322221111")
            check("n-m = ", n - m, "123456789012345678844445555666677778889")
            check("n / m = ", n / m, "2222266652000240026")
            check("n % m = ", n % m, "43398759628555611114")
            check("m*(n / m)+(n % m) = ", m * (n / m) + (n % m), ns)
            let two64 = Integer(-2) ** 64
            check("2**64 = ", two64, "18446744073709551616")
            check("2**64.isPowerOfTwo = ", "\(two64.isPowerOfTwo)", "true")
            if two64.isPowerOfTwo {
                check("2**64 binary exponent = ", "\(two64.trailingZeroBitCount)", "64")
            }
            check("(2**64-1).isPowerOfTwo = ", "\((two64-1).isPowerOfTwo)", "false")
            let ffff = Integer("-0xFFFF")   // or 0x-FFFF will also work
            check("-FFFF = ", ffff, "-65535")
            check2("-FFFF = ", ffff, 16, "-FFFF")
            let n2 = Integer("-10000000000000", withBase:10)
            check("-10000000000000 = ", n2, "-10000000000000")
            let n3 = Integer("-10000000000000000", withBase: 2)
            check("-10000000000000000B = ", n3, "-65536")
            check2("-10000000000000000B = ", n3, 2, "-10000000000000000")
            check("-8**3 = ", -8 ** 3, "-512")
            check("69! = ", Integer(69).factorial(), "171122452428141311372468338881272839092270544893520369393648040923257279754140647424000000000000000")
            check("69! -> Dump = ", Integer(69).factorial().debugDescription, "size=11, digits=0 0 208483648 1760158 815281888 388340220 147380948 549955052 405677315 320051255 84005611 , base=1073741824")
            let n4 = Integer("123456789012345")
            check("GCD(\(n4), 87654321) = ", n4.gcd(Integer(87654321)), "3")
            print("Random(50) = \(Integer.random())")
            check("Integer(987654321) = ", Integer(987654321098765432), "987654321098765432")
            check("zero setBit 128 = ", Integer.zero.setBit(128), "340282366920938463463374607431768211456")
            check("one clearBit 0 = ", Integer.one.clearBit(0), "0")
            check("zero toggleBit 16 = ", Integer.zero.toggleBit(16), "65536")
            check("~1 = ", ~Integer.one, "-2")
            check("~0 = ", ~Integer.zero, "-1")
            check("-1 & 0xFFFF = ", Integer(-1) & 0xFFFF, "65535")
            check("-1 & -2 = ", Integer(-1) & Integer(-2), "-2")
            
            check("9 % 4 = ", Integer(9) % Integer(4), "1")
            check("-9 % 4 = ", Integer(-9) % Integer(4), "-1")
            check("9 % -4 = ", Integer(9) % Integer(-4), "1")
            check("-9 % -4 = ", Integer(-9) % Integer(4), "-1")
            
            check("Integer(1.23456789e+18) = ", Integer(1.23456789e+18), "1234567890000000000")
            
            print("Integer sequence in for loop: ")
            for i in Integer(1)...Integer(4) { print(i) }
            
            let x = Integer("1234567890000000000")
            let x² = Integer("1524157875019052100000000000000000000")
            check("sqrt(\(x²)) =", x².sqrt(), x.description)
            check("\(x).sqr() =", x.sqr(), x².description)
            
            print("Finding a prime number:")
            var prime = false
            repeat {
                let a = Integer.random(bits:32) | 1
                print("Integer.random(bits:32) =", a)
                prime = a.isPrime
                print("\(a) is\(prime ? "" : " not") prime")
            } while !prime

        }
        
//        func testPerformanceFromString() {
//            var x = Integer()
//            let s = "1711224524281413113724683388812728390922705448935203693936480409232572797541406474240000000000000001"
//            self.measure {
//                // Put the code you want to measure the time of here.
//                for _ in 1...100 { x = Integer(s) }
//            }
//            print(x)
//        }
        
//        func testSquaring1() {
//            let x = Integer("1711224524281413113724683388812728390922705448935203693936480409232572797541406474240000000000000001")
//            var y = Integer.zero
//            self.measure {
//                for _ in 1...1000 { y = x*x }
//            }
//            print(y)
//        }
//
//        func testSquaring2() {
//            let x = Integer("1711224524281413113724683388812728390922705448935203693936480409232572797541406474240000000000000001")
//            var y = Integer.zero
//            self.measure {
//                for _ in 1...1000 { y = x.sqr() }
//            }
//            print(y)
//        }
        
//        func testPerformanceFactorial() {
//            // This is an example of a performance test case.
//            let x = Integer(999)
//            self.measure {
//                // Put the code you want to measure the time of here.
//                _ = x.factorial()
//            }
//        }
        
    }

