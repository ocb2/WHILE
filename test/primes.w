p := 0;
n := 2;

while (~p = 100) {
    d := 2;
    t := 0;

    while (d < n) {
        if (n % d = 0) {
            d := n;
            t := 1
        } else {
            d := d + 1
        }
    };

    if (t = 0) {
        p := p + 1;
        out n
    } else {
        skip
    };

    n := n + 1
}