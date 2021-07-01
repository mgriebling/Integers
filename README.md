# Integers

Implements integer values of arbitrary magnitude.  Includes all standard arithmetic and logic operations.
A preliminary version of rational numbers is also included with basic arithmetic operations.

Copyright © 2002, 2003, 2015 Michael van Acken and Michael Griebling

This module is free software; you can redistribute it and/or modify it under the terms of the GNU Lesser General Public License as published by the Free Software Foundation; either version 2 of the License, or (at your option) any later version.

This module is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License along with Integers. If not, write to the Free Software Foundation, 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

This module is a reformulation of (parts of) Python's *longobject.c* in Swift.  Optimizations like Karatsuba multiplication and string conversion for power of two base have been omitted.  All errors are mine, of course.

Added algorithms are from Knuth: "The Art Of Computer Programming", Vol 2, section 4.3.1

Ported to Swift by Michael Griebling, 18 July 2015.
