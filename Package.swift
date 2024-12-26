// swift-tools-version:5.3
// The swift-tools-version declares the minimum version of Swift required to build this package.

import PackageDescription

let package = Package(
    name: "Integers",
	platforms: [
		// required to support StaticBigInt - wish there were a way to fallback to Int
		.macOS("13.3"), .iOS("16.4"), .tvOS("16.4"), .watchOS("9.4"),
		// .macCatalyst("13.3")
	],
    products: [
        // Products define the executables and libraries a package produces, and make them visible to other packages.
        .library(
            name: "Integers",
            targets: ["Integers"]),
    ],
    dependencies: [
        // Dependencies declare other packages that this package depends on.
        // .package(url: /* package url */, from: "1.0.0"),
        // .package(url: "https://github.com/jph00/BaseMath.git", .upToNextMajor(from: "1.0.0")),
    ],
    targets: [
        // Targets are the basic building blocks of a package. A target can define a module or a test suite.
        // Targets can depend on other targets in this package, and on products in packages this package depends on.
        .target(
            name: "Integers",
            dependencies: []),
        .testTarget(
            name: "IntegersTests",
            dependencies: ["Integers"]),
    ]
)
