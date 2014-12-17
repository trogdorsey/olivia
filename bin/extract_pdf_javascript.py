#!/usr/bin/python

import glob
import os
import sys 

import olivia


def extract_pdf_js(files):

    for f in files:
        data = ''
        if os.path.exists(f):
            fin = open(f, 'r')
            data = fin.read()
            fin.close()
        else:
            print f, "not found"

        mypdf = olivia.olivia(data, f, '')
        mypdf.DEBUG = True
        if mypdf.is_valid():
            mypdf.parse()
            decoded, decoded_headers, sloppy = mypdf.get_javascript()

            if len(decoded) > 0:
                js = decoded + decoded_headers
                jsfile = open(f + '.javascript', 'w')
                if jsfile:
                    print 'Wrote JavaScript (%d bytes -- %d headers / %d code) to file %s' % (len(js), len(decoded_headers), len(decoded), f + '.javascript') 
                    jsfile.write(js)
                    jsfile.close()
            else:
                print 'Didnt decode any JavaScript within PDF file'
        else:
            print('warn: ignoring non-pdf file ' + f)


if __name__ == '__main__':
    for i in sys.argv[1:]:
        extract_pdf_js(glob.glob(i))
