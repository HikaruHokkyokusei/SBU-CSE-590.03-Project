use vstd::prelude::*;

verus! {
    struct Constants {
        z: i64
    }

    struct Variables {
        x: i64,
        y: i64
    }

    spec fn init(u: Variables) -> bool {
        u.x == 0 && u.y == 5
    }

    spec fn moved_north(u: Variables, v: Variables) -> bool {
        v.x == u.x && v.y == u.y + 1
    }

    spec fn moved_south_east(u: Variables, v: Variables) -> bool {
        v.y == u.y - 1 && v.x == u.x + 1
    }

    enum Movement {
        North,
        SouthEast
    }

    spec fn is_valid_movement(u: Variables, v: Variables, movement: Movement) -> bool {
        match movement {
            Movement::North => moved_north(u, v),
            Movement::SouthEast => moved_south_east(u, v)
        }
    }

    spec fn next(u: Variables, v: Variables) -> bool {
        exists |movement: Movement| is_valid_movement(u, v, movement)
    }

    spec fn in_manhole(u: Variables) -> bool {
        u.x * u.x + u.y * u.y <= 3
    }

    spec fn safety(u: Variables) -> bool {
        !in_manhole(u)
    }

    spec fn inductive(u: Variables) -> bool {
        u.x + u.y >= 5
    }

    fn main() { }
}
