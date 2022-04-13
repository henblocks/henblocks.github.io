function testFindFirstDiffPos() {
    let index, pos;

    [index, pos] = findFirstDiffPos("", "");
    console.assert(index === null);
    console.assert(pos === null);

    [index, pos] = findFirstDiffPos("abc", "abc");
    console.assert(index === null);
    console.assert(pos === null);

    [index, pos] = findFirstDiffPos("a", "abc");
    console.assert(index === 1);
    console.assert(pos.line === 0);
    console.assert(pos.ch === 1);

    [index, pos] = findFirstDiffPos("abc", "a");
    console.assert(index === 1);
    console.assert(pos.line === 0);
    console.assert(pos.ch === 1);

    [index, pos] = findFirstDiffPos("abcdefg\nqwerty", "abcdefg\nabcdefg");
    console.assert(index === 8);
    console.assert(pos.line === 1);
    console.assert(pos.ch === 0);
}

function testCartesianProduct() {
    console.assert(cartesianProduct([]).length === 0);

    let result;

    result = cartesianProduct(["A"], ["B"]);
    console.assert(result.length === 1);
    console.assert(result[0].length === 2);
    console.assert(result[0][0] === "A");
    console.assert(result[0][1] === "B");

    result = cartesianProduct(["A", "B"], ["C", "D"]);
    console.assert(result.length === 4);
    console.assert(result[0].length === 2);
    console.assert(result[0][0] === "A");
    console.assert(result[0][1] === "C");
    console.assert(result[1][0] === "A");
    console.assert(result[1][1] === "D");
    console.assert(result[2][0] === "B");
    console.assert(result[2][1] === "C");
    console.assert(result[3][0] === "B");
    console.assert(result[3][1] === "D");
}

testFindFirstDiffPos();
testCartesianProduct();