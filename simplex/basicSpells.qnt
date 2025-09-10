// -*- mode: Bluespec; -*-
/**
 * This module collects definitions that are ubiquitous.
 * One day they will become the standard library of Quint.
 */
module basicSpells {
  /// Option type, which may hold some value or none
  type Option[a] = Some(a) | None

  /// An annotation for writing preconditions.
  /// - @param cond condition to check
  /// - @returns true if and only if cond evaluates to true
  pure def require(cond: bool): bool = cond

  run requireTest = all {
    assert(require(4 > 3)),
    assert(not(require(false))),
  }

  /// A convenience operator that returns a string error code,
  ///  if the condition does not hold true.
  ///
  /// - @param cond condition to check
  /// - @param error a non-empty error message
  /// - @returns "", when cond holds true; otherwise error
  pure def requires(cond: bool, error: str): str = {
    if (cond) "" else error
  }

  run requiresTest = all {
    assert(requires(4 > 3, "4 > 3") == ""),
    assert(requires(4 < 3, "false: 4 < 3") == "false: 4 < 3"),
  }


  /// Compute the maximum of two integers.
  ///
  /// - @param i first integer
  /// - @param j second integer
  /// - @returns the maximum of i and j
  pure def max(i: int, j: int): int = {
    if (i > j) i else j
  }

  run maxTest = all {
    assert(max(3, 4) == 4),
    assert(max(6, 3) == 6),
    assert(max(10, 10) == 10),
    assert(max(-3, -5) == -3),
    assert(max(-5, -3) == -3),
  }

  /// Compute the minimum of two integers.
  ///
  /// - @param i first integer
  /// - @param j second integer
  /// - @returns the minimum of i and j
  pure def min(i: int, j: int): int = {
    if (i < j) i else j
  }

  run minTest = all {
    assert(min(3, 4) == 3),
    assert(min(6, 3) == 3),
    assert(min(10, 10) == 10),
    assert(min(-3, -5) == -5),
    assert(min(-5, -3) == -5),
  }

  /// Compute the absolute value of an integer
  ///
  /// - @param i : an integer whose absolute value we are interested in
  /// - @returns |i|, the absolute value of i
  pure def abs(i: int): int = {
    if (i < 0) -i else i
  }

  run absTest = all {
    assert(abs(3) == 3),
    assert(abs(-3) == 3),
    assert(abs(0) == 0),
  }

  /// Remove a set element.
  ///
  /// - @param s a set to remove an element from
  /// - @param elem an element to remove
  /// - @returns a new set that contains all elements of set but elem
  pure def setRemove(s: Set[a], elem: a): Set[a] = {
    s.exclude(Set(elem))
  }

  run setRemoveTest = all {
    assert(Set(2, 4) == Set(2, 3, 4).setRemove(3)),
    assert(Set() == Set().setRemove(3)),
  }

  /// Adds an element to a set.
  ///
  /// - @param s a set to add an element to
  /// - @param elem an element to add
  /// - @returns a new set that contains all elements of set and elem
  pure def setAdd(s: Set[a], elem: a): Set[a] = {
    s.union(Set(elem))
  }

  run setAddTest = all{
    assert(Set(2, 3, 4) == Set(2, 4).setAdd(3)),
    assert(Set(3) == Set().setAdd(3)),
    assert(Set(2,4) == Set(2,4).setAdd(4)),
  }

  /// Test whether a key is present in a map
  ///
  /// - @param m a map to query
  /// - @param key the key to look for
  /// - @returns true if and only map has an entry associated with key
  pure def has(m: a -> b, key: a): bool = {
    m.keys().contains(key)
  }

  run hasTest = all {
    assert(Map(2 -> 3, 4 -> 5).has(2)),
    assert(not(Map(2 -> 3, 4 -> 5).has(6))),
  }

  /// Get the map value associated with a key, or the default,
  /// if the key is not present.
  ///
  /// - @param m the map to query
  /// - @param key the key to search for
  /// - @returns the value associated with the key, if key is
  ///   present in the map, and default otherwise
  pure def getOrElse(m: a -> b, key: a, default: b): b = {
    if (m.has(key)) {
      m.get(key)
    } else {
      default
    }
  }

  run getOrElseTest = all {
    assert(Map(2 -> 3, 4 -> 5).getOrElse(2, 0) == 3),
    assert(Map(2 -> 3, 4 -> 5).getOrElse(7, 11) == 11),
  }

  /// Remove a map entry.
  ///
  /// - @param m a map to remove an entry from
  /// - @param key the key of an entry to remove
  /// - @returns a new map that contains all entries of map
  ///          that do not have the key key
  pure def mapRemove(m: a -> b, key: a): a -> b = {
    m.keys().setRemove(key).mapBy(k => m.get(k))
  }

  run mapRemoveTest = all {
    assert(Map(3 -> 4, 7 -> 8) == Map(3 -> 4, 5 -> 6, 7 -> 8).mapRemove(5)),
    assert(Map() == Map().mapRemove(3)),
  }

  /// Removes a set of map entries.
  ///
  /// - @param m a map to remove entries from
  /// - @param ks a set of keys for entries to remove from the map
  /// - @returns a new map that contains all entries of map
  ///          that do not have a key in keys
  pure def mapRemoveAll(m: a -> b, ks: Set[a]): a -> b = {
      m.keys().exclude(ks).mapBy(k => m.get(k))
  }

  run mapRemoveAllTest =
      val m = Map(3 -> 4, 5 -> 6, 7 -> 8)
      all {
          assert(m.mapRemoveAll(Set(5, 7)) == Map(3 -> 4)),
          assert(m.mapRemoveAll(Set(5, 99999)) == Map(3 -> 4, 7 -> 8)),
      }

  /// Get the set of values of a map.
  ///
  /// - @param map a map from type a to type b
  /// - @returns the set of all values in the map
  pure def values(m: a -> b): Set[b] = {
    m.keys().map(k => m.get(k))
  }

  run valuesTest = all {
    assert(values(Map()) == Set()),
    assert(values(Map(1 -> 2, 2 -> 3)) == Set(2, 3)),
    assert(values(Map(1 -> 2, 2 -> 3, 3 -> 2)) == Set(2, 3)),
  }

  /// Whether a set is empty
  ///
  /// - @param s a set of any type
  /// - @returns true iff the set is the empty set
  pure def empty(s: Set[a]): bool = s == Set()

  run emptyTest = all {
    assert(empty(Set()) == true),
    assert(empty(Set(1, 2)) == false),
    assert(empty(Set(Set())) == false),
  }

  pure def filterMap(s: Set[a], f: (a) => Option[b]): Set[b] = {
    s.fold(Set(), (acc, e) => {
      match f(e) {
        | Some(x) => acc.union(Set(x))
        | None => acc
      }
    })
  }
}