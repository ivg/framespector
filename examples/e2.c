int bar(int x1, int x2, int x3,
        int x4, int x5, int x6,
        int x7, int x8, int x9) {
    return x1-x2-x3-x4-x5-x6-x7-x8-x9;
}


int foo(int x1, int x2, int x3,
        int x4, int x5, int x6,
        int x7, int x8, int x9) {
    int r = bar(x9,x8,x7,x6,x5,x4,x3,x2,x1);
    return x1+x2+x3+x4+x5+x6+x7+x8+x9-r;
}

int main(void) {
    return foo(1,2,3,4,5,6,7,8,9);
}
