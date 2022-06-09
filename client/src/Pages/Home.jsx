
import React from 'react';
import fruits from '../fruits.json';
import SearchBar from '../components/SearchBar/SearchBar';

function HomePage() { 
    return (
        <div className="App">
            <div className='upper-box'>
                <div>
                    <h2>FRUITS PRICE PREDICTION</h2>
                    <div className='some-text'>The avocado is a fleshy exotic fruit obtained from the tropical tree of the same name. In some parts of South America it is known as Palta. It measures 5-6 cm in length. The normal weight ranges between 200-400 g, although there are some units that weigh up to 2 kg. The skin is thick and tough, of a green colour; the tone depends on the variety. The oily pulp of cream to greenish-yellow colour has a very similar taste to nuts. It has a single round seed of pale brown colour, 2-4 cm long.</div>
                </div>
                <div className='avocado-image'></div>
            </div>
            <div>
                <SearchBar placeholder='Search fruit..' data={fruits} />
            </div>
        </div>
    )
}

export default HomePage;