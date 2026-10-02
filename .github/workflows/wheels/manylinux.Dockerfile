# Toolchain for the Linux wheel (release.yml builds it once and caches it on ghcr.io)
FROM quay.io/pypa/manylinux2014_x86_64
RUN yum install -y devtoolset-11 gperf ccache tcl-devel zlib-devel libffi-devel elfutils-devel elfutils-libelf-devel libdwarf-devel
ENV PATH=/opt/rh/devtoolset-11/root/usr/bin:/opt/python/cp313-cp313/bin:$PATH

# CentOS 7's bison and flex are too old for Yosys
RUN cd /tmp && curl -L https://ftp.gnu.org/gnu/bison/bison-3.8.2.tar.gz | tar -xz && cd bison-3.8.2 && ./configure && make -j$(nproc) install
RUN cd /tmp && curl -L https://github.com/westes/flex/releases/download/v2.6.4/flex-2.6.4.tar.gz | tar -xz && cd flex-2.6.4 && ./configure && make -j$(nproc) install

# Verific's tclmain links -lnsl
RUN echo "void dummy_nsl(void){}" | gcc -shared -o /usr/lib64/libnsl.so -x c -
RUN pip install wheel packaging 'pybind11>=3,<4' 'cxxheaderparser>=1.4' auditwheel && git config --system --add safe.directory '*'
