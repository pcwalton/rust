/*

<script type="text/javascript" src="zepto.js"></script>
<script type="text/javascript" src="playground.js"></script>

*/
    
    var elems = {};
    $(function() {
        [ 'alt', 'ret', 'mod', 'str' ].forEach(function(keyword) {
            elems[keyword] = [];
            $(".Statement").add(".Type").each(function(index, item) {
                if (item.innerHTML.indexOf(keyword) !== -1) {
                    elems[keyword].push(item);
                }
                return true;
            });
        });

        $("body").append(
            "<div style='position: fixed; top: 0; right: 0;'>" +
            "<button onclick='change(\"alt\")'>Change 'alt'</button>" +
            "<button onclick='change(\"ret\")'>Change 'ret'</button>" +
            "<button onclick='change(\"mod\")'>Change 'mod'</button>" +
            "<button onclick='change(\"str\")'>Change 'str'</button>" +
            "</div>"
        );

    });

    function change(keyword) {
        var to = prompt("Change '" + keyword + "' to what?", keyword);
        elems[keyword].forEach(function(elem) {
            elem.innerHTML = to;
        });
    }

