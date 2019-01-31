var ALPHABET = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";
var MAX_DEGREE = 32;

var STEP_BY_NODE = 0,
    STEP_BY_EDGE = 1,
    FINAL_GRAPH = -1;

var BOTTOM= 0,
    TOP = 1,
    RANDOM = 2;

//Distributions
var UNIFORM = 0;

Array.prototype.containsLink = function(obj) {
  var arr = Object(this);
    for(var i = 0; i < arr.length; i++) {
      if (obj.source === arr[i].source && obj.target === arr[i].target)
        return true;
    }
  return false;
}

var seq = [];
var width = 640,
    height = 480;

var edges = [],
    nodes = [],
    buckets = [];

var stepSize = STEP_BY_NODE,
    selectMethod = BOTTOM,
    placeMethod = BOTTOM;

var isGraphic = function(seq) {
  seq.sort( (a, b) => b - a );    
  if ( seq[ seq.length - 1 ] < 0) return false;
  if ( seq[ 0 ] >= seq.length) return false;
  if ( seq[ 0 ] === 0) return true;
  if ( seq[ seq[ 0 ] ] < 1 ) return false;
  
  var j = seq.shift();
  for (var i = 0; i < j; i++)
    seq[i] -= 1;
  
  return isGraphic(seq);
}

var generateLabel = function(index) {
   var divisior = ALPHABET.length,
       dividend = parseInt(index / divisior),
       remainder = index % divisior;
  var label = ALPHABET[remainder];
  for (var i = 0; i < dividend; i++) {
    label += "'";
  }
  return label;
}

var randIndex = function(length, probDist, formula) {
  switch (probDist) {
    case UNIFORM:
      return parseInt(Math.floor( Math.random() * length));
    default:
      return 0;
  }
}

var makeNodes = function(sequence) {
  return sequence.map( (elm, index) => ({ id: index, label:generateLabel(index), degree: elm, edgeWith:[]}) );
}

var bucketize = function(nodes) {
  var buckets = [],
      counter = 0;
  for(var i = 0; i < MAX_DEGREE; i++) {
    buckets.push([]);
    for(var j = 0; j < nodes.length; j++) {
      if(nodes[j].degree === i) {
        buckets[i].push(nodes[j]);
        counter++;
      }
    }
    if (counter == nodes.length)
      break;
  }
  return buckets;
}

// Removes extra buckets and makes sure next node is available
// Returns index of current max degree (zero-based, hence equal to max degree) or -1 when no nodes are available
var sanitizeBuckets = function(buckets) {
  var maxDegree = buckets.length;
  while (buckets[--maxDegree].length < 1) {}
  return maxDegree;
}

var edgeExists = function(source, target) {
  for (var i = 0; i < source.edgeWith.length; i++)
    if (source.edgeWith[i] == target.id)
      return true;
  for (var i = 0; i < target.edgeWith.length; i++)
    if (target.edgeWith[i] == source.id)
      return true;
  return false;
}

var nextSource = function(buckets, method, probDist, probDistFormula) {
  var bucketPointer = sanitizeBuckets(buckets);
  if(bucketPointer < 1) {
    return undefined; // or should throw error
  }
  switch(method) {
    case BOTTOM:
      return buckets[bucketPointer].shift();
    case TOP:
      return buckets[bucketPointer].pop();
    // Probability Distribution
    case RANDOM:
      return buckets[bucketPointer].splice(randIndex(buckets[bucketPointer].length, probDist, probDistFormula), 1)[0];
    default:
      return undefined;
  }
}

var nextTarget = function(source, buckets, method, probDist, probDistFormula) {
  var bucketPointer = sanitizeBuckets(buckets);
  if(bucketPointer < 1) {
    return undefined; // or should throw error
  }
  switch(method) {
    case BOTTOM:
      var i = -1;
      while ( edgeExists(source, buckets[bucketPointer][++i]) ) {
        if (i == buckets[bucketPointer].length - 1) {
          bucketPointer--;
          i = -1;
        }    
      }
      return buckets[bucketPointer].splice(i, 1)[0];
      
    case TOP:
      var i = buckets[bucketPointer].length;
      while ( edgeExists(source, buckets[bucketPointer][--i]) )
        if (i == 0) {
          bucketPointer--;
          i = buckets[bucketPointer].length;
        }    
      return buckets[bucketPointer].splice(i, 1)[0];
      
    // Probability Distribution
    case RANDOM:
      var candidates = [];
      var i = -1;
      for ( var i = 0; i < buckets[bucketPointer].length; i++) {
        if ( !edgeExists(source, buckets[bucketPointer][i]) )
          candidates.push(buckets[bucketPointer][i])
        if (i == buckets[bucketPointer].length - 1 && candidates.length == 0 ) {
          bucketPointer--;
          i = 0;
        }
      }
      var index = buckets[bucketPointer].indexOf(candidates.splice(randIndex(candidates.length, probDist, probDistFormula), 1)[0]);
      return buckets[bucketPointer].splice(index, 1)[0];
    default:
      return undefined;
  }
}

var placeNode = function(node, buckets, method, probDist, probDistFormula) {
  var bucketPointer = node.degree;
  if(buckets[bucketPointer] == undefined) {
    throw 'Buckets are not sanitized!';
  }
  switch(method) {
    case BOTTOM:
      buckets[bucketPointer].unshift(node);
      break;
    case TOP:
      buckets[bucketPointer].push(node);
      break;
    case RANDOM:
      var  i = randIndex(buckets[bucketPointer].length, probDist, probDistFormula);
      buckets[bucketPointer].splice(i, 0, node);
      console.log(JSON.parse(JSON.stringify(buckets)));
      break;
    default:
      break;
  }
}

var stepGraph = function(buckets, selectMethod, placeMethod, stepsSize, probDist, probDistFormula) {
  
  var edges = [],
      interim = [];

  var source = nextSource(buckets, selectMethod, probDist, probDistFormula);
  if(!source) {
    return [];
  }
  interim.push(source);
  var iters = (stepsSize) ? stepsSize : source.degree;
  for (var i = 0; i < iters; i++) {
    var target = nextTarget(source, buckets, selectMethod, probDist, probDistFormula);
    if (!target)
      throw "The degree sequence is not graphic!";
    edges.push( {source: source.id, target: target.id, value: 1} );
    source.edgeWith.push(target.id);
    source.degree--;
    target.degree--;
    interim.push(target);
  }
  while (interim.length > 0)
    placeNode(interim.shift(), buckets, placeMethod, probDist, probDistFormula);
  return edges;
}

function generateGraph(sequence) {
  if(buckets.length < 1) {
    nodes = makeNodes(sequence);
    buckets = bucketize(nodes);
  }
  switch(stepSize) {
    case STEP_BY_NODE:
      edges.push.apply(edges, stepGraph(buckets, selectMethod, placeMethod, STEP_BY_NODE, UNIFORM));
      break;
    case STEP_BY_EDGE:
      edges.push.apply(edges, stepGraph(buckets, selectMethod, placeMethod, STEP_BY_EDGE, UNIFORM));
      break;
    case FINAL_GRAPH:
      while ((res = stepGraph(buckets, selectMethod, placeMethod, STEP_BY_NODE, UNIFORM)).length > 0 )
        edges.push.apply(edges, res);
  }
    
  drawGraph();
}

function drawGraph() {
  
  var nodesDraw = JSON.parse(JSON.stringify(nodes));
  var edgesDraw = JSON.parse(JSON.stringify(edges));
  
  for (var i = 0; i < nodesDraw.length; i++) {
    for (var j = i+1; j < nodesDraw.length; j++)
      edgesDraw.push({source: nodesDraw[i].id, target: nodesDraw[j].id, value: 0});
  }
  
  var graphContainter = d3.select('#graphs').append('div');
  graphContainter.append('hr');
  var containter = graphContainter.append('div')
                                    .attr('class', 'd-flex justify-content-center space-after');
  
  var svg = containter.append('svg')
    .attr('width', width)
    .attr('height', height);
  
  // init force layout
  var force = d3.layout.force()
    .size([width, height])
    .nodes(nodesDraw) // initialize with a single node
    .links(edgesDraw)
    .linkDistance(width/4)
    .friction(0.001)
    .charge(10);
  
  var link = svg.selectAll('.link')
    .data(edgesDraw)
    .enter().append('line')
    .attr('class', 'link')
    .attr('stroke-width', function(d) { return d.value} );

  var node = svg.selectAll('.node')
    .data(nodesDraw)
    .enter().append('g')
    .call(force.drag);
  
  node.append("circle")
    .attr("class", 'node')
    .attr("r", "20");
  
  node.append("text")
    .attr("y", "8")
    .attr("class", "node-label")
    .attr("text-anchor", "middle")
    .attr("font-size", "22px")
    .text( function(d) { return d.label })
  
  force.on('tick', function() {
  
    node.attr("transform", function(d) { return "translate(" + d.x + "," + d.y + ")"; });

    link.attr('x1', function(d) { return d.source.x; })
        .attr('y1', function(d) { return d.source.y; })
        .attr('x2', function(d) { return d.target.x; })
        .attr('y2', function(d) { return d.target.y; });
  
  });
  force.start();

}

$('#deg-input').on('keydown', function(e) { 
  var keyCode = e.keyCode || e.which; 
  if (keyCode == 9) { 
    e.preventDefault(); 
    $(this).val().split(",").map( elm => {elm = parseInt(elm); if (!isNaN(elm)) seq.push(parseInt(elm));} );
    $(this).val('');
    $('#seq-string').text( seq.join(" , "));
  }
  
  if ((keyCode == 8 || keyCode == 46) && $(this).val() == "") { 
    e.preventDefault(); 
    seq.pop();
    $(this).val('');
    $('#seq-string').text( seq.join(" , ") );
  } 
});

$('#select-method').on('change', function(e) { e.preventDefault(); selectMethod = parseInt($(this).val()); });
$('#place-method').on('change', function(e) { e.preventDefault(); placeMethod = parseInt($(this).val()); });

$('#step-by-edge').on('click', function(e) {
  e.preventDefault();
  if (isGraphic(seq.slice(0))) {
    stepSize = STEP_BY_EDGE;
    generateGraph(seq);
  } else {
    alert("This sequence is not graphic!");
  }
});

$('#step-by-node').on('click', function(e) {
  e.preventDefault();
  if (isGraphic(seq.slice(0))) {
    stepSize = STEP_BY_NODE;
    generateGraph(seq);
  } else {
    alert("This sequence is not graphic!");
  }
});

$('#final-graph').on('click', function(e) {
  e.preventDefault();
  if (isGraphic(seq.slice(0))) {
      stepSize = FINAL_GRAPH;
      generateGraph(seq);
  } else {
    alert("This sequence is not graphic!");
  }

});

$('#reset').on('click', function(e) {
  e.preventDefault();
  seq.length = 0;
  $('#graphs').text('');
  $('#seq-string').text('');
});
