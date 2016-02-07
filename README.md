#FixFile

This is a library for datatype-generic file serialization.

##Features

* Transaction-isolation via Multi-Version Concurrency Control (MVCC).
* Append-only file format with a cavuum (garbage collection) feature.
* Lazy reads that only read structures that are accessed.
* Writes that only write modified structures.
* Clear separation between I/O and manipulation of data structures.
* Standard library providing implementations of sets and key-value stores.

