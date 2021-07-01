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
                XCTAssert(n.description == m, "\(a)\(n) -> FAIL!")
            }
            
            func check2 (_ a: String, _ n: Integer, _ base: Int, _ m: String) {
                XCTAssert(n.description(base) == m, "\(a)\(n.description(base)) -> FAIL!")
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
            check("2^64 = ", 2 ** 64, "18446744073709551616")
            let ffff = Integer("-0xFFFF")   // or 0x-FFFF will also work
            check("-FFFF = ", ffff, "-65535")
            check2("-FFFF = ", ffff, 16, "-FFFF")
            let n2 = Integer("-10000000000000", withBase:10)
            check("-10000000000000 = ", n2, "-10000000000000")
            let n3 = Integer("-10000000000000000", withBase: 2)
            check("-10000000000000000B = ", n3, "-65536")
            check2("-10000000000000000B = ", n3, 2, "-10000000000000000")
            check("-8^3 = ", -8 ** 3, "-512")
            check("69! = ", Integer(69).factorial(), "171122452428141311372468338881272839092270544893520369393648040923257279754140647424000000000000000")
            let n4 = Integer("123456789012345")
            check("GCD(123456789012345, 87654321) = ", n4.gcd(Integer(87654321)), "3")
    //        let n5 = "\(Integer.random())"
    //        print("Random(50) = \(Integer.random())")
            check("Integer(987654321) = ", Integer(987654321), "987654321")
            check("zero SetBit 128 = ", Integer.zero.setBit(128), "340282366920938463463374607431768211456")
            check("one ClearBit 0 = ", Integer.one.clearBit(0), "0")
            check("zero ToggleBit 16 = ", Integer.zero.toggleBit(16), "65536")
            check("~1 = ", ~Integer.one, "-2")
            check("~0 = ", ~Integer.zero, "-1")
            check("-1 & 0xFFFF = ", Integer(-1) & 0xFFFF, "65535")
            check("-1 & -2 = ", Integer(-1) & Integer(-2), "-2")
        }
        
        func testPerformanceFactorial() {
            // This is an example of a performance test case.
            let x = Integer(1000)
            self.measure {
                // Put the code you want to measure the time of here.
                _ = x.factorial()
            }
        }
        
    }

