var fs = require('fs');
var file = fs.readFileSync('source_index.c',"utf8");
var result = [];
var flip = false;
file.split("```c").forEach(function(each){
  if(flip) {
    var temp = each.split('```');
    temp[0] = temp[0].replace(/</g,"%lt");
    temp[0] = temp[0].replace(/>/g,"%gt");
    result.push(temp.join('```'));
  } else {
    result.push(each);
    flip = true;
  }
});

fs.writeFileSync('index.html',result.join("```c"));
