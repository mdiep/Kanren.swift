
extension AnyIterator {
    public init(values: [Element]) {
        var values: [Element] = values.reversed()
        self.init { return values.popLast() }
    }
    
    public static func interleave<I: IteratorProtocol>(_ iterators: [I]) -> AnyIterator<Element> where I.Element == Element {
        var iterators = iterators.map(AnyIterator.init)
        return AnyIterator {
            while let i = iterators.first {
                iterators.remove(at: 0)
                if let result = i.next() {
                    iterators.append(i)
                    return result
                }
            }
            return nil
        }
    }
}

extension IteratorProtocol {
    public func flatMap(_ transform: @escaping (Element) -> AnyIterator<Element>) -> AnyIterator<Element> {
        var outer = self
        var inner = outer.next().map(transform)
        return AnyIterator {
            while let i = inner {
                if let result = i.next() {
                    return result
                }
                inner = outer.next().map(transform)
            }
            return nil
        }
    }
}
