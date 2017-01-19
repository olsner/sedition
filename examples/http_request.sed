# Just the request parsing bit from the http server, this should work the same
# in GNU sed.

    1 {
        /^GET ([^ ]*) / {
            # TODO Implement and rely on sed saving the last regexp
            s//\1/
            h
            #s/.*/Got URL &/p
            d
        }
        i broken
        broken
    }

    s/\r$//
    2,/^$/ {
        #i reading header
        #p
        /^Host: (.*)/ {
            #i got host
            s//\1/
            G
            s,(.*)\n(.*),http://\1\2,
            h
            #s/.*/Got full URL &/p
            z
        }
        /^$/ breq
        d
    }

    :req
    i\
HTTP/1.0 200 OK\r\
Content-Type: text/plain\r\
\r\
Hello world!\
Requested URL was:
    g
    p
    b done

    :roken
    i\
400 Bad request\r\
\r\
Go away.
    b done

    :done
    q
