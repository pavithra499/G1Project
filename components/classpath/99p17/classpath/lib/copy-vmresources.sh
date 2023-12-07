#! /bin/bash
# lib/copy-vmresources.sh.  Generated from copy-vmresources.sh.in by configure.

top_srcdir=..
vmdirs=`echo "${top_srcdir}/vm/reference" | sed 's%:% %g'`
destMetaDir=`pwd`/META-INF
destResDir=`pwd`

for p in ${vmdirs}; do
	if test -d $p/META-INF; then
		(cd $p/META-INF; 
		 dirs=`find . -name "CVS" -prune -o -type d -print`;
		 for u in ${dirs}; do
			 /usr/bin/mkdir -p ${destMetaDir}/${u};
		 done;
		 files=`find . -name "CVS" -prune -o -name "*.in" -prune -o -type f -print`;
		 for u in ${files}; do
			 cp ${u} ${destMetaDir}/${u};
		 done
		 );
	fi;

	(cd ${p};
	  resfiles=`find . -name "*.properties"`
	  resdirs=
	  for i in ${resfiles}; do 
		  a=`basename ${i}`; 
		  b=`echo ${i} | sed "s%${a}%%g"`; 
	  	  resdirs="${resdirs} ${b}";
	  done;
  	  resnewdirs=`echo ${resdirs} | uniq`;

  	  for u in ${resnewdirs}; do
  		  /usr/bin/mkdir -p ${destResDir}/${u};
  	  done
  
	  for f in ${resfiles}; do
		echo ${f} ${destResDir}/${f};
	  done
	  )
done