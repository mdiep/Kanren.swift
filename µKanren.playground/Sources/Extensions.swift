
extension AnyIterator {
    public init(values: [Element]) {
        var values: [Element] = values.reversed()
        self.init { return values.popLast() }
    }
}

extension IteratorProtocol {
    public func flatMap(_ transform: (Element) -> AnyIterator<Element>) -> AnyIterator<Element> {
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
    
    public func interleave<I: IteratorProtocol where I.Element == Element>(with iterator: I) -> AnyIterator<Element> {
        var iterators = [ AnyIterator(self), AnyIterator(iterator) ]
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
