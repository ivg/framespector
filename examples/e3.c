#include <stdio.h>
#include <stdlib.h>

int foo(int one, int two, int three, int four,
        int five, int six, int seven, int eight)
{
    return one + two + three + four + five + six + seven + eight;
}

int main(int argc, char *argv[]) {
    int one, two, three, four, five, six, seven, eight;
    one = 1; two = 2; three = 3; four = 4; five = 5;
    six = 6; seven = 7;
    eight = atoi(argv[1]);
    return foo(one, two, three, four, five, six, seven, eight);
}
