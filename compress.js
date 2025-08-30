// dont even ask why this is here
const fs = require("fs");
const LZString = require("lz-string");

let data = "";
process.stdin.setEncoding("utf8");
process.stdin.on("data", chunk => data += chunk);
process.stdin.on("end", () => {
  data = data.replace(/\r\n/g, "\n");
  const compressed = LZString.compressToBase64(data);
  process.stdout.write(compressed);
});
