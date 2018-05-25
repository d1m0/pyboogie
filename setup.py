import setuptools

with open("README.md", "r") as fh:
    long_description = fh.read()

setuptools.setup(
    name="pyboogie",
    version="0.0.1",
    author="Dimitar Bounov",
    author_email="dimitar.bounov@gmail.com",
    license="GPL",
    description="Implementation of a core subset of the Boogie language.",
    long_description=long_description,
#    long_description_content_type="text/markdown",
    url="https://github.com/d1m0/pyboogie",
    packages=setuptools.find_packages(),
    install_requires=["z3-solver", "pyparsing", "mypy", "frozendict", "pyro4"],
    python_requires=">=3",
    classifiers=(
        "Programming Language :: Python :: 3",
        "License :: OSI Approved :: GNU General Public License (GPL)",
    ),
)